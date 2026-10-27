/// Passive physical spelling of immutable representations published by Baker.
/// This module has no native type resolver, range selector or target state.
module Alex.CodeGeneration.TypeMapping

open Fidelity.PSG
open Alex.Dialects.Core.Types

let numericProjection (graph: Revision) =
    graph.Emission.Numeric

let scalarCarrierAt (graph: Revision) (nodeId: NodeId) : ScalarCarrier option =
    let publication = numericProjection graph
    match publication.Values.TryFind nodeId with
    | Some carrier -> Some carrier
    | None ->
        match publication.Unresolved.TryFind nodeId with
        | Some reason -> failwithf "TypeMapping: Numeric carrier at node %d is unresolved: %s" (NodeId.value nodeId) reason
        | None when publication.Required.Contains nodeId ->
            failwithf "TypeMapping: source Numeric publication omitted the required carrier at node %d" (NodeId.value nodeId)
        | None -> None

let settledScalarType (slot: SettledSlot) : MLIRType option = SettledScalar.tryType slot

let isResourceRepresentation = function
    | ValueRepresentation.Scalar(SettledSlot.CHandle _) -> true
    | ValueRepresentation.Union(cases, _) ->
        cases |> List.exists (fun (_, payloads) ->
            payloads |> List.exists (function ValueRepresentation.Scalar(SettledSlot.CHandle _) -> true | _ -> false))
    | _ -> false

let isResourceOccurrence (graph: Revision) nodeId =
    graph.Emission.Numeric.OccurrenceRepresentations.TryFind nodeId
    |> Option.exists (function Ok representation -> isResourceRepresentation representation | Error _ -> false)

let scalarCarrierType (carrier: ScalarCarrier) : MLIRType =
    settledScalarType carrier.Slot
    |> Option.defaultWith (fun () -> failwithf "TypeMapping: source carrier at node %d has no admitted scalar physical form: %A" (NodeId.value carrier.Site) carrier.Slot)

let rec representationType = function
    | ValueRepresentation.Scalar slot ->
        settledScalarType slot |> Option.defaultWith (fun () -> failwithf "TypeMapping: source scalar form has no physical spelling: %A" slot)
    | ValueRepresentation.Buffer(None, element) -> TMemRef(representationType element)
    | ValueRepresentation.Buffer(Some count, element) when count >= 0 -> TMemRefStatic(count, representationType element)
    | ValueRepresentation.Buffer(Some count, _) -> failwithf "TypeMapping: source buffer has negative extent %d" count
    | ValueRepresentation.Record(fields, placement) ->
        let bytes = placement |> Option.map (fun (offsets, size, alignment) -> { Offsets = offsets; Size = size; Align = alignment })
        TStruct(fields |> List.map (fun (name, form) -> name, representationType form), bytes)
    | ValueRepresentation.CallableComponent(_, data) -> representationType data
    | ValueRepresentation.Union(cases, Some(_, bytes, alignment)) as representation when
        cases.Length = 2 && bytes > 0 && alignment > 0
        && (cases |> List.filter (snd >> List.isEmpty) |> List.length) = 1
        && (cases |> List.filter (function
            | _, [ValueRepresentation.Scalar(SettledSlot.CHandle(_, bits, handleAlignment))] -> bits > 0 && handleAlignment > 0
            | _ -> false) |> List.length) = 1 ->
        TResourceOption representation
    | ValueRepresentation.Union(cases, _) when
        cases |> List.exists (fun (_, payloads) ->
            payloads |> List.exists (function ValueRepresentation.Scalar(SettledSlot.CHandle _) -> true | _ -> false)) ->
        failwith "TypeMapping: resource option requires its complete source-settled case and byte placement"
    | ValueRepresentation.Union(_, Some(_, bytes, alignment)) when bytes >= 0 && alignment > 0 ->
        TMemRefStatic(bytes, TInt(IntWidth 8))
    | ValueRepresentation.Union _ -> failwith "TypeMapping: source union has no complete physical data placement"
    | ValueRepresentation.Tag cases when cases > 0 -> TTag cases
    | ValueRepresentation.Tag _ -> failwith "TypeMapping: source tag has no cases"

let private read what = function
    | Some(Ok form) -> representationType form
    | Some(Error reason) -> failwithf "TypeMapping: %s has no source-published representation: %s" what reason
    | None -> failwithf "TypeMapping: source publication omitted %s" what

/// The native entry and import own the physical function type. Numeric's
/// callable refusal is not an entry representation and remains unchanged.
let nativeEntrySlotType (graph: Revision) (storage: ProgramStorageEntry) =
    match storage.Shape with
    | ProgramStorageShape.NativeEntry formation ->
        let boundary = graph.Emission.Boundary

        match boundary.Entries.TryFind formation with
        | Some entry when entry.Formation = formation && entry.SourceType = storage.SourceType ->
            match boundary.Imports.TryFind entry.Import, boundary.Loading with
            | Some imported, Some loading when
                imported.Binding = entry.Declaration
                && entry.Loading = loading.Identity
                && imported.Library = loading.Contract.Library
                ->
                Ok(entry, TFunc(BoundaryAbi.parameters imported, BoundaryAbi.results imported))
            | _ -> Error "Native entry slot has no matching current import and selected loading account."
        | _ -> Error "Native entry slot has no matching current source formation."
    | _ -> Error "Native entry slot requires its source-issued native entry storage shape."

let private nativeSlotValueType (graph: Revision) nodeId =
    let projection = graph.Emission.Storage

    match projection.ProgramStorage.Entries.TryFind(ProgramStorageIdentity.BindingSlot nodeId) with
    | Some storage when
        (match storage.Shape with
         | ProgramStorageShape.NativeEntry _ -> true
         | _ -> false)
        ->
        let entry, functionType =
            nativeEntrySlotType graph storage
            |> Result.defaultWith (fun reason -> failwithf "TypeMapping: %s" reason)

        let binding = graph.Nodes.TryFind nodeId

        if
            not projection.ProgramStorage.Unresolved.IsEmpty
            || not (projection.SlotAuthorities.Contains nodeId)
        then
            failwith "TypeMapping: Native entry slot lacks its source-settled storage authority."

        match binding with
        | Some node when
            node.Type = storage.SourceType
            && entry.Transport.Contains nodeId
            && node.Children = [ entry.Formation ]
            && (match node.Kind with
                | SemanticKind.Binding(_, false, _, _) -> true
                | _ -> false)
            ->
            Some functionType
        | _ -> failwith "TypeMapping: Native entry slot differs from its original immutable formation binding."
    | _ -> None

let valueTypeAt (graph: Revision) (nodeId: NodeId) =
    match nativeSlotValueType graph nodeId with
    | Some functionType -> functionType
    | None ->
        (numericProjection graph).OccurrenceRepresentations.TryFind nodeId
        |> read (sprintf "value occurrence %d" (NodeId.value nodeId))

/// A pointer occurrence must publish its scalar form directly. Generic callable
/// component unwrapping cannot establish this contract for the occurrence.
let pointerTypeAt (graph: Revision) (nodeId: NodeId) =
    match (numericProjection graph).OccurrenceRepresentations.TryFind nodeId with
    | Some(Ok(ValueRepresentation.Scalar(SettledSlot.Pointer 1) as form)) -> representationType form
    | Some(Ok _) ->
        failwithf "TypeMapping: value occurrence %d has no source-published scalar pointer representation" (NodeId.value nodeId)
    | other -> read (sprintf "value occurrence %d" (NodeId.value nodeId)) other

let typeOfIdentity (graph: Revision) (identity: TypeIdentity) =
    (numericProjection graph).TypeRepresentations.TryFind identity |> read "type identity"

let sourceTypeAt (graph: Revision) (nodeId: NodeId) =
    (numericProjection graph).SourceTypes.TryFind nodeId
    |> Option.defaultWith (fun () -> failwithf "TypeMapping: source publication omitted type identity at %d" (NodeId.value nodeId))

let settledLayoutFor (graph: Revision) (identity: TypeIdentity) =
    (numericProjection graph).Layouts.TryFind identity

let settledLayoutAt graph nodeId = settledLayoutFor graph (sourceTypeAt graph nodeId)

let nodeWidth graph nodeId =
    match scalarCarrierAt graph nodeId with
    | Some { Slot = SettledSlot.Integer(bits, _) } when bits > 0 -> Some(IntWidth bits)
    | Some { Slot = SettledSlot.Integer _ } -> failwith "TypeMapping: source integer width is not positive"
    | _ -> None

let requireNodeWidth graph nodeId =
    nodeWidth graph nodeId |> Option.defaultWith (fun () -> failwithf "TypeMapping: no published integer carrier at %d" (NodeId.value nodeId))

/// A container's physical byte view follows its published aggregate placement.
let physicalStorageType (_arch: Architecture) = function
    | TStruct(_, Some bytes) -> TMemRefStatic(bytes.Size, TInt(IntWidth 8))
    | TStruct _ -> failwith "TypeMapping: an aggregate storage view requires complete source byte placement"
    | ty -> ty
