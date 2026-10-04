/// Passive transport of source-settled callable components in records and unions.
/// Only the published selector and environment views enter aggregate data storage.
module Alex.Patterns.CallableAggregatePatterns

open Fidelity.PSG
open XParsec
open XParsec.Parsers
open XParsec.Combinators
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.XParsec.PSGCombinators
open Alex.CodeGeneration.TypeMapping
open Alex.Elements.MLIRAtomics
open Alex.Elements.ArithElements
open Alex.Elements.FuncElements
open Alex.Elements.SCFElements
open Alex.Elements.CFElements
open Alex.Elements.MemRefElements
module Values = Alex.Traversal.Values
module Operands = Alex.Traversal.CallableOperands

let hasRows (graph: Revision) occurrence = graph.Emission.Callable.AggregateValues.ContainsKey occurrence

let private refusal occurrence slot code message =
    let route = slot |> Option.map (fun identity -> $" at resolved slot {NodeId.value identity}") |> Option.defaultValue ""
    Diagnostic.coded code (Some occurrence) (Some "CallableAggregate") (Some "operation commitment") (message + route)

let private fieldName (graph: Revision) aggregate ordinal =
    match graph.Emission.Numeric.OccurrenceRepresentations.TryFind aggregate with
    | Some(Result.Ok(ValueRepresentation.Record(fields, _))) -> List.tryItem ordinal fields |> Option.map fst
    | _ -> None

let private caseName (graph: Revision) aggregate ordinal =
    match graph.Emission.Numeric.OccurrenceRepresentations.TryFind aggregate with
    | Some(Result.Ok(ValueRepresentation.Union(cases, _))) -> List.tryItem ordinal cases |> Option.map fst
    | _ -> None

/// The field/case is part of the identity: equal input values in different
/// fields cannot cause an ordinary data field to disappear from construction.
let recordInputIsCallable (graph: Revision) occurrence name value =
    graph.Emission.Callable.AggregateValues.TryFind occurrence
    |> Option.exists (List.exists (fun row ->
        row.Value = Some value &&
        (graph.Emission.Callable.AggregateSlots.TryFind row.Slot |> Option.exists (fun slot ->
            match slot.Path with
            | [CallableAggregatePathStep.RecordField ordinal] -> fieldName graph row.Aggregate ordinal = Some name
            | _ -> false))))

let unionInputIsCallable (graph: Revision) occurrence caseIndex value =
    graph.Emission.Callable.AggregateValues.TryFind occurrence
    |> Option.exists (List.exists (fun row ->
        row.Value = Some value &&
        (graph.Emission.Callable.AggregateSlots.TryFind row.Slot |> Option.exists (fun slot ->
            slot.Path = [CallableAggregatePathStep.UnionPayload(caseIndex, 0)]))))

let private alternative (graph: Revision) (row: CallableAggregateValue) (arm: CallableAggregateAlternative) =
    let projection = graph.Emission.Callable
    let error text = Result.Error(refusal row.Occurrence (Some row.Slot) AX4001 text)
    match projection.AggregateSlots.TryFind row.Slot, projection.Carriers.TryFind arm.Carrier with
    | Some slot, Some carrier
        when carrier.Formation = arm.Formation && carrier.EnvironmentValue = arm.EnvironmentValue &&
             carrier.Contract = slot.Contract && slot.Contract = Result.Ok arm.Contract ->
        match slot.Contract |> Result.toOption |> Option.bind projection.Contracts.TryFind with
        | Some contract when contract.Kind = carrier.Kind ->
            // R3-M1: this is the single native-reconstruction admission guard.
            if carrier.Kind <> CallableKind.OrdinaryFlatClosure then
                let message = $"Callable aggregate {row.Operation}: the callable receiving contract is published, but native callable-component reconstruction is not admitted by this witness pathway."
                Result.Error(refusal row.Occurrence (Some row.Slot) AX4002 message)
            elif arm.Adapter.IsSome then
                error "Callable aggregate adapters require an explicit source-authored relation."
            elif carrier.EnvironmentValue.IsSome <> arm.EnvironmentPlacement.IsSome ||
                 carrier.Environment.IsSome <> arm.EnvironmentPlacement.IsSome then
                error "Callable aggregate alternative lost its explicit environment presence."
            elif not (arm.EnvironmentPlacement |> Option.forall (fun placement ->
                Some placement.Value = carrier.EnvironmentValue &&
                (carrier.Environment |> Option.exists (fun environment -> environment.Owner = placement.Owner)) &&
                contract.EnvironmentBytes = Some placement.ViewBytes && placement.Adaptation.IsNone)) then
                error "Callable aggregate environment view lacks its exact source-owned convention."
            else Result.Ok carrier
        | _ -> error "Callable aggregate alternative lacks its receiving contract."
    | _ -> error "Callable aggregate alternative lost its paired formation, environment or contract."

let private operationErrors (graph: Revision) occurrence operation (row: CallableAggregateValue) =
    let error text = refusal occurrence (Some row.Slot) AX4001 text
    let projection = graph.Emission.Callable
    let reading = row.Operation = CallableAggregateOperation.Project || row.Operation = CallableAggregateOperation.Snapshot
    let writing = row.Operation = CallableAggregateOperation.Construct && row.Aggregate = occurrence
    let tagCurrent =
        row.Tag |> Option.exists (fun tag ->
            let constructor =
                match graph.Nodes.TryFind tag.Constructor with
                | Some { Kind = SemanticKind.DUConstruct(_, ordinal, payload, _) }
                | Some { Kind = SemanticKind.UnionCase(_, ordinal, payload) } ->
                    tag.CaseOrdinal = ordinal && tag.Payload = payload &&
                    tag.PayloadOrdinal = (payload |> Option.map (fun _ -> 0))
                | _ -> false
            constructor &&
            (tag.TagRead |> Option.forall (fun read ->
                match graph.Nodes.TryFind read with
                | Some { Kind = SemanticKind.DUGetTag(subject, _) } -> subject = row.Aggregate
                | _ -> false)))
    match projection.AggregateSlots.TryFind row.Slot with
    | None -> [error "Callable aggregate transport lacks its resolved slot."]
    | Some slot ->
        match slot.Path, operation with
        | [CallableAggregatePathStep.RecordField ordinal], SemanticKind.RecordExpr(fields, _) ->
            let supplied =
                fieldName graph row.Aggregate ordinal
                |> Option.map (fun name -> fields |> List.filter (fst >> (=) name))
                |> Option.defaultValue []
            [ if not writing || row.Tag.IsSome then
                  yield error "Callable record construction has a changed operation, destination or tag."
              match supplied with
              | [(_, value)] when row.Value = Some value -> ()
              | [] -> yield error "A copied callable field has no explicit source-authored copy relation."
              | _ -> yield error "Callable record construction differs from its witnessed field operand." ]
        | [CallableAggregatePathStep.RecordField ordinal], SemanticKind.FieldSet(aggregate, name, value) ->
            [ if row.Operation <> CallableAggregateOperation.Assign || row.Aggregate <> aggregate ||
                 fieldName graph aggregate ordinal <> Some name || row.Value <> Some value || row.Tag.IsSome then
                  yield error "Callable record assignment differs from its witnessed aggregate, field or value operand." ]
        | [CallableAggregatePathStep.RecordField ordinal], SemanticKind.FieldGet(aggregate, name) ->
            [ if not reading || row.Aggregate <> aggregate || fieldName graph aggregate ordinal <> Some name || row.Tag.IsSome then
                  yield error "Callable record projection differs from its witnessed aggregate or field operand." ]
        | [CallableAggregatePathStep.UnionPayload(callableCase, 0)], SemanticKind.DUConstruct(name, ordinal, payload, _)
        | [CallableAggregatePathStep.UnionPayload(callableCase, 0)], SemanticKind.UnionCase(name, ordinal, payload) ->
            [ if not writing || caseName graph row.Aggregate ordinal <> Some name || not tagCurrent ||
                 not (row.Tag |> Option.exists (fun tag -> tag.Constructor = occurrence && tag.CaseOrdinal = ordinal && tag.Payload = payload)) then
                  yield error "Callable union construction differs from its witnessed constructor, tag or payload."
              if callableCase = ordinal then
                  if row.Alternatives.IsEmpty || row.Value <> payload then
                      yield error "Callable union construction differs from its witnessed callable payload."
              elif not row.Alternatives.IsEmpty || row.Value.IsSome || row.Selector.IsSome || row.SelectedAlternative.IsSome then
                  yield error "An absent callable union case invents a callable payload or selector." ]
        | [CallableAggregatePathStep.UnionPayload(callableCase, 0)], SemanticKind.DUEliminate(aggregate, ordinal, name, _) ->
            [ if not reading || row.Aggregate <> aggregate || callableCase <> ordinal ||
                 caseName graph aggregate ordinal <> Some name || row.Alternatives.IsEmpty || not tagCurrent ||
                 not (row.Tag |> Option.exists (fun tag -> tag.CaseOrdinal = ordinal && tag.Payload.IsSome)) then
                  yield error "Callable union projection differs from its witnessed aggregate, case, tag or payload." ]
        | _, SemanticKind.DUInitialize _ ->
            [error "Callable destination initialization has no explicit source-authored transport relation."]
        | _ -> [error "Callable aggregate transport has no published slot matching its witnessed operation."]

// Enumerate the already-published representation value, never source nodes or
// callable origins. A component's data fields are not further code components.
let rec private componentIdentities = function
    | ValueRepresentation.CallableComponent(identity, _) -> [identity]
    | ValueRepresentation.Record(fields, _) -> fields |> List.collect (snd >> componentIdentities)
    | ValueRepresentation.Union(cases, _) -> cases |> List.collect (snd >> List.collect componentIdentities)
    | ValueRepresentation.Buffer(_, element) -> componentIdentities element
    | _ -> []

/// Missing rows cannot turn a callable component into ordinary data. Only the
/// selected published field/case is examined for a projection or assignment.
let requiresComponents (graph: Revision) occurrence operation =
    let representation id =
        graph.Emission.Numeric.OccurrenceRepresentations.TryFind id
        |> Option.orElseWith (fun () ->
            graph.Emission.Numeric.SourceTypes.TryFind id
            |> Option.orElseWith (fun () -> graph.Nodes.TryFind id |> Option.map _.Type)
            |> Option.bind graph.Emission.Numeric.TypeRepresentations.TryFind)
        |> Option.bind Result.toOption
    let contains representation = not (componentIdentities representation).IsEmpty
    let field aggregate name =
        representation aggregate |> Option.exists (function
            | ValueRepresentation.Record(fields, _) -> fields |> List.exists (fun (heldName, value) -> heldName = name && contains value)
            | _ -> false)
    let selectedCase aggregate ordinal name =
        representation aggregate |> Option.exists (function
            | ValueRepresentation.Union(cases, _) ->
                cases |> List.mapi (fun index (heldName, payloads) -> (index = ordinal || heldName = name) && List.exists contains payloads)
                |> List.exists id
            | _ -> false)
    if hasRows graph occurrence then true else
    match operation with
    | SemanticKind.RecordExpr _ | SemanticKind.DUConstruct _ | SemanticKind.UnionCase _ ->
        representation occurrence |> Option.exists contains
    | SemanticKind.FieldGet(aggregate, name) | SemanticKind.FieldSet(aggregate, name, _) -> field aggregate name
    | SemanticKind.DUEliminate(aggregate, ordinal, name, _) -> selectedCase aggregate ordinal name
    | SemanticKind.DUInitialize(destination, _, _, _) -> representation destination |> Option.exists contains
    | _ -> false

let private copyErrors (graph: Revision) occurrence operation (rows: CallableAggregateValue list) =
    match operation, graph.Emission.Numeric.OccurrenceRepresentations.TryFind occurrence with
    | SemanticKind.RecordExpr(fields, Some _), Some(Result.Ok(ValueRepresentation.Record(declared, _))) ->
        declared |> List.collect (fun (name, representation) ->
            componentIdentities representation |> List.choose (fun identity ->
                let bound = rows |> List.filter (fun row -> row.Slot = identity)
                let supplied = fields |> List.filter (fst >> (=) name)
                match bound, supplied with
                | [row], [(_, value)] when row.Value = Some value -> None
                | _ ->
                    let diagnostic = refusal occurrence (Some identity) AX4001 "A copied callable field has no explicit source-authored copy relation and operation-bound replacement."
                    Some diagnostic))
    | SemanticKind.RecordExpr(_, Some _), _ ->
        [refusal occurrence None AX4001 "Callable copy/update has no complete published record representation."]
    | _ -> []

/// Read only the published account and the observed operation. This performs
/// no source analysis, origin recovery, layout selection or ABI inference.
let validateOperation (graph: Revision) occurrence (operation: SemanticKind) =
    let projection = graph.Emission.Callable
    let error text = refusal occurrence None AX4001 text
    match graph.Nodes.TryFind occurrence, projection.AggregateValues.TryFind occurrence, projection.AggregateDependencies.TryFind occurrence with
    | Some current, Some rows, Some account
        when current.Kind = operation && not rows.IsEmpty && account.Occurrence = occurrence &&
             (account.Values |> List.filter (fun row -> row.Occurrence = occurrence)) = rows ->
        let failures =
            [ if rows |> List.exists (fun row -> row.Occurrence <> occurrence) then
                  yield error "Callable aggregate row names another occurrence."
              if account.Values |> List.exists (fun row ->
                    projection.AggregateValues.TryFind row.Occurrence |> Option.forall (not << List.contains row)) then
                  yield error "Callable aggregate dependency account has a changed value row."
              if account.Slots |> List.exists (fun slot -> projection.AggregateSlots.TryFind slot.Identity <> Some slot) then
                  yield error "Callable aggregate dependency account has a changed slot."
              if account.Carriers |> List.exists (fun carrier -> projection.Carriers.TryFind carrier.Occurrence <> Some carrier) then
                  yield error "Callable aggregate dependency account has a changed formation."
              if account.Contracts |> List.exists (fun contract -> projection.Contracts.TryFind contract.Identity <> Some contract) then
                  yield error "Callable aggregate dependency account has a changed receiving contract."
              if account.Symbols |> List.exists (fun (implementation, symbol) -> projection.Symbols.TryFind implementation <> Some symbol) then
                  yield error "Callable aggregate dependency account has a changed implementation symbol."
              if (account.Flows |> List.exists (fun flow -> projection.Flows.TryFind flow.Occurrence <> Some flow)) ||
                 (account.Joins |> List.exists (fun join -> projection.Joins.TryFind join.Occurrence <> Some join)) then
                  yield error "Callable aggregate dependency account has a changed flow or join."
              if (account.Sources |> List.exists (fun source ->
                    graph.Nodes.TryFind source.Node |> Option.forall (fun node ->
                        source.Kind <> node.Kind || source.Type <> node.Type || source.Children <> node.Children || source.Anchors <> node.ObligationAnchors))) ||
                 (account.Claims |> List.exists (fun (id, claim) -> graph.CurrentClaims.TryFind id <> Some claim)) then
                  yield error "Callable aggregate dependency account has changed source or proof evidence."
              yield! copyErrors graph occurrence operation rows
              for row in rows do
                  yield! operationErrors graph occurrence operation row
                  for arm in row.Alternatives do
                      match alternative graph row arm with
                      | Result.Ok _ -> ()
                      | Result.Error diagnostic -> yield diagnostic ]
        match failures with
        | failure :: _ -> Result.Error failure
        | [] -> Result.Ok rows
    | _ -> Result.Error(error "Callable aggregate transport lacks its current published dependency account and observed operation.")

let private pRows occurrence operation = parser {
    let! state = getUserState
    do! ensure (state.Current.Id = occurrence && state.Zipper.Focus.Id = occurrence && state.Current.Kind = operation)
            "Callable aggregate transport requires its actual Huet occurrence and operation."
    match validateOperation state.Graph occurrence operation with
    | Result.Ok rows -> return rows
    | Result.Error diagnostic -> return! fail (Message diagnostic.Message)
}

let private pAlternative row arm = parser {
    let! state = getUserState
    match alternative state.Graph row arm with
    | Result.Ok carrier -> return carrier
    | Result.Error diagnostic -> return! fail (Message diagnostic.Message)
}
let private pSelector (row: CallableAggregateValue) = parser {
    let! selector =
        match row.Selector with
        | Some selector when selector.Lower = 0 && selector.UpperExclusive = row.Alternatives.Length &&
                             (row.Alternatives |> List.map _.Ordinal) = [0 .. row.Alternatives.Length - 1] -> preturn selector
        | _ -> fail (Message "Callable aggregate selector has no exact alternative domain.")
    match selector.Storage, selector.Slot, selector.ByteOffset with
    | None, None, None when row.Alternatives.Length = 1 -> return None
    | Some _, Some(SettledSlot.Integer _ as slot), Some offset when offset >= 0 ->
        match settledScalarType slot with
        | Some ty -> return Some(offset, ty)
        | None -> return! fail (Message "Callable aggregate selector has no published integer carrier.")
    | _ -> return! fail (Message "Callable aggregate selector has no complete source placement.")
}

let private pReceivingType (row: CallableAggregateValue) = parser {
    let! state = getUserState
    let projection = state.Graph.Emission.Callable
    let! contract =
        match projection.AggregateSlots.TryFind row.Slot with
        | Some slot ->
            match slot.Contract |> Result.toOption |> Option.bind projection.Contracts.TryFind with
            | Some contract -> preturn contract
            | None -> fail (Message "Callable aggregate slot has no published receiving convention.")
        | None -> fail (Message "Callable aggregate has no published slot.")
    let expected = [0 .. contract.ParameterTypes.Length - 1] |> List.filter (fun ordinal -> not (List.contains ordinal contract.OmittedParameters))
    do! ensure (List.map fst contract.ParameterRepresentations = expected)
            "Callable aggregate receiving contract has no exact physical parameter inventory."
    let arguments = contract.ParameterRepresentations |> List.map (snd >> representationType)
    do! ensure (arguments |> List.forall ((<>) TVoid))
            "Callable aggregate receiving convention omitted no parameter at a physical unit slot."
    let result = representationType contract.ResultRepresentation
    return TFunc(arguments, if result = TVoid then [] else [result])
}

let private pStorage (row: CallableAggregateValue) (value: Val) = parser {
    let! state = getUserState
    let! slot =
        match state.Graph.Emission.Callable.AggregateSlots.TryFind row.Slot with
        | Some slot when state.Graph.Emission.Numeric.SourceTypes.TryFind row.Aggregate = Some slot.AggregateType -> preturn slot
        | _ -> fail (Message "Callable component storage has no exact enclosing type identity.")
    let! representation =
        match state.Graph.Emission.Numeric.OccurrenceRepresentations.TryFind row.Aggregate with
        | Some(Result.Ok representation) -> preturn representation
        | _ -> fail (Message "Callable component storage has no published aggregate representation.")
    let parent = { value with Type = physicalStorageType state.Platform.TargetArch value.Type }
    do! ensure (parent.Type = (representationType representation |> physicalStorageType state.Platform.TargetArch))
            "Callable component storage differs from its published enclosing data representation."
    // The authored ordinal route and each published parent placement determine
    // the views. This fold walks no source nodes and computes no byte layout.
    let! operations, storage, leaf =
        (preturn ([], parent, representation), slot.Path |> List.indexed)
        ||> List.fold (fun prior (depth, step) -> parser {
            let! operations, parent, representation = prior
            let! offset, child =
                match step, representation with
                | CallableAggregatePathStep.RecordField ordinal, ValueRepresentation.Record(fields, Some(offsets, _, _)) ->
                    match List.tryItem ordinal fields, List.tryItem ordinal offsets with
                    | Some(_, child), Some offset -> preturn (offset, child)
                    | _ -> fail (Message "Callable record component has no published declaration-ordinal placement.")
                | CallableAggregatePathStep.UnionPayload(caseOrdinal, 0), ValueRepresentation.Union(cases, Some(offset, _, _)) ->
                    match List.tryItem caseOrdinal cases with
                    | Some(_, [child]) -> preturn (offset, child)
                    | _ -> fail (Message "Callable union component requires its exact single-payload placement.")
                | _ -> fail (Message "Callable component route lacks a published record/union data layout.")
            let name = Values.aggregateComponent row.Occurrence row.Slot depth
            match child with
            | ValueRepresentation.CallableComponent(identity, ValueRepresentation.Record(_, Some(_, bytes, alignment)))
                when identity = row.Slot && depth = slot.Path.Length - 1 && bytes = row.Bytes && alignment = row.Alignment ->
                if bytes = 0 then return operations, parent, child
                else
                    let result = { SSA = name 60; Type = TMemRefStatic(bytes, TInt(IntWidth 8)) }
                    let! literal = pConstI (name 61) (int64 offset) TIndex
                    let! view = pMemRefView result.SSA parent.SSA (name 61) parent.Type result.Type
                    return operations @ [literal; view], result, child
            | ValueRepresentation.Record _ | ValueRepresentation.Union _ ->
                let childType = representationType child |> physicalStorageType state.Platform.TargetArch
                let result = { SSA = name 50; Type = childType }
                let! loads = pTypedExtractView result.SSA parent.SSA offset (name 51) (name 52) (name 53) childType parent.Type
                return operations @ loads, result, child
            | _ -> return! fail (Message "Callable component route does not end at its exact component data representation.")
        })
    do! ensure (row.Bytes >= 0 && row.Alignment > 0 &&
                (match leaf with ValueRepresentation.CallableComponent(identity, _) -> identity = row.Slot | _ -> false))
            "Callable aggregate component differs from its source-published placement."
    return operations, storage
}

let private pWrite (ctx: WitnessContext) (destination: Val) (row: CallableAggregateValue) = parser {
    do! ensure (row.Operation = CallableAggregateOperation.Construct || row.Operation = CallableAggregateOperation.Assign)
            "Callable aggregate write lacks a settled construction or assignment event."
    if row.Alternatives.IsEmpty then
        let! state = getUserState
        let absent =
            match state.Graph.Emission.Callable.AggregateSlots.TryFind row.Slot, row.Tag with
            | Some { Path = CallableAggregatePathStep.UnionPayload(caseOrdinal, _) :: _ }, Some tag -> tag.CaseOrdinal <> caseOrdinal
            | _ -> false
        do! ensure (row.Selector.IsNone && row.Value.IsNone && row.SelectedAlternative.IsNone &&
                    absent)
                "An absent union payload must have neither a callable value nor a selector."
        return []
    else
        let! state = getUserState
        let! alternative, actual =
            match row.SelectedAlternative, row.Value with
            | Some selected, Some value ->
                match row.Alternatives |> List.filter (fun alternative -> alternative.Ordinal = selected) with
                | [alternative] -> preturn (alternative, value)
                | _ -> fail (Message "Callable aggregate write has no unique selected source alternative.")
            | _ -> fail (Message "Callable aggregate write lacks its exact source value and selected alternative.")
        let! carrier = pAlternative row alternative
        let! value =
            match MLIRAccumulator.recallCallable actual state.Accumulator with
            | Some value when Operands.exactCarrier value = Some carrier -> preturn value
            | _ -> fail (Message "Callable aggregate write did not witness its exact paired source value.")
        let! shape =
            match Operands.project ctx actual with
            | Result.Ok shape -> preturn shape
            | Result.Error reason -> fail (Message reason)
        let! receivingType = pReceivingType row
        do! ensure ((Operands.code value).Type = Operands.functionType shape && receivingType = Operands.functionType shape)
                "Callable aggregate write has a changed function convention."
        let! storageOps, destination = pStorage row destination
        let name = Values.aggregateComponent row.Occurrence row.Slot alternative.Ordinal
        let! environmentOps =
            match alternative.EnvironmentPlacement, Operands.environment value with
            | None, None -> preturn []
            | Some placement, Some environment when environment.Type = TMemRefStatic(placement.ViewBytes, TInt(IntWidth 8)) ->
                pTypedInsertView destination.SSA environment.SSA placement.ByteOffset (name 0) (name 1) (name 2)
                                 environment.Type destination.Type
            | _ -> fail (Message "Callable aggregate write lost its actual environment operand.")
        let! selector = pSelector row
        let! selectorOps =
            match selector with
            | None -> preturn []
            | Some(offset, ty) -> parser {
                let! constant = pConstI (name 3) (int64 alternative.Ordinal) ty
                let! stores = pTypedInsertView destination.SSA (name 3) offset (name 4) (name 5) (name 6) ty destination.Type
                return constant :: stores
              }
        return storageOps @ environmentOps @ selectorOps
}

/// Compose writes into the aggregate data value already allocated by its owner.
let pWriteComponents (ctx: WitnessContext) occurrence operation destination = parser {
    let! rows = pRows occurrence operation
    let! writes = rows |> List.map (pWrite ctx destination) |> Alex.XParsec.Extensions.sequence
    return List.concat writes
}

let pWithConstruction (ctx: WitnessContext) occurrence operation
                      (construction: PSGParser<MLIROp list * TransferResult>) = parser {
    let! _ = pRows occurrence operation
    let! operations, result = construction
    match result with
    | TRValue destination ->
        let! writes = pWriteComponents ctx occurrence operation destination
        return operations @ writes, result
    | _ -> return! fail (Message "Callable aggregate construction has no witnessed data storage.")
}

let pAssignComponents (ctx: WitnessContext) occurrence operation = parser {
    let! _ = pRows occurrence operation
    let! aggregate =
        match operation with
        | SemanticKind.FieldSet(aggregate, _, _) -> preturn aggregate
        | _ -> fail (Message "Callable assignment requires its witnessed field-set operation.")
    let! source, sourceType = pRecallNode aggregate
    let! writes = pWriteComponents ctx occurrence operation { SSA = source; Type = sourceType }
    return writes, TRVoid
}

/// A fold over published alternatives spells conditional regions. It does not
/// traverse source code or derive a dispatch family. The final arm is admitted
/// only after its selector comparison succeeds. No unknown tag supplies code.
let private pSelect (row: CallableAggregateValue) lane (selector: Val option)
                    (arms: (int * MLIROp list * Val) list) = parser {
    match arms, selector with
    | [(_, operations, value)], None -> return operations, value
    | _ :: _, Some selector ->
        let finalOrdinal, finalOps, finalValue = List.last arms
        let finalName = Values.aggregateComponent row.Occurrence row.Slot finalOrdinal
        let! finalLiteral = pConstI (finalName lane) (int64 finalOrdinal) selector.Type
        let! finalCompare = pCmpI (finalName (lane + 1)) ICmpPred.Eq selector.SSA (finalName lane) selector.Type
        let! finalAssert = pAssert (finalName (lane + 1)) "Callable aggregate selector is outside its published alternative domain."
        let checkedFinalOps = [finalLiteral; finalCompare; finalAssert] @ finalOps
        let! operations, result =
            (arms |> List.take (arms.Length - 1), preturn (checkedFinalOps, finalValue))
            ||> List.foldBack (fun (ordinal, operations, value) rest -> parser {
                let! fallbackOps, fallbackValue = rest
                do! ensure (value.Type = fallbackValue.Type)
                        "Callable aggregate alternatives lack a source-settled common physical convention."
                let name = Values.aggregateComponent row.Occurrence row.Slot ordinal
                let constant, condition = name lane, name (lane + 1)
                let result = { SSA = name (lane + 2); Type = value.Type }
                let! literal = pConstI constant (int64 ordinal) selector.Type
                let! compare = pCmpI condition ICmpPred.Eq selector.SSA constant selector.Type
                let! selectedYield = pSCFYield [value.SSA, value.Type]
                let! fallbackYield = pSCFYield [fallbackValue.SSA, fallbackValue.Type]
                let! conditional = pSCFIf condition (operations @ [selectedYield])
                                            (Some(fallbackOps @ [fallbackYield])) (Some(result.SSA, result.Type))
                return [literal; compare; conditional], result
            })
        return operations, result
    | _ -> return! fail (Message "Callable aggregate selection has no complete arm/selector correspondence.")
}

let pReadComponent (ctx: WitnessContext) occurrence operation = parser {
    let! state = getUserState
    let! rows = pRows occurrence operation
    let! aggregate =
        match operation with
        | SemanticKind.FieldGet(aggregate, _)
        | SemanticKind.DUEliminate(aggregate, _, _, _) -> preturn aggregate
        | _ -> fail (Message "Callable projection requires its witnessed field or union projection.")
    let! row =
        match rows with
        | [row] when row.Aggregate = aggregate &&
                     (row.Operation = CallableAggregateOperation.Project || row.Operation = CallableAggregateOperation.Snapshot) -> preturn row
        | _ -> fail (Message "Callable aggregate read has no unique published slot and snapshot frontier.")
    let! raw, rawType = pRecallNode aggregate
    let! storageOps, storage = pStorage row { SSA = raw; Type = rawType }
    let! shape =
        match Operands.project ctx occurrence with
        | Result.Ok shape -> preturn shape
        | Result.Error reason -> fail (Message reason)
    let! receivingType = pReceivingType row
    do! ensure (receivingType = Operands.functionType shape)
            "Callable aggregate read differs from its exact receiving convention."
    let! selector = pSelector row
    let! selectorOps, selectorValue =
        match selector with
        | None -> preturn ([], None)
        | Some(offset, ty) -> parser {
            let name = Values.aggregateComponent occurrence row.Slot 0
            let value = { SSA = name 10; Type = ty }
            let! loads = pTypedExtractView value.SSA storage.SSA offset (name 11) (name 12) (name 13) ty storage.Type
            return loads, Some value
          }
    let! arms =
        row.Alternatives |> List.map (fun alternative -> parser {
            let! carrier = pAlternative row alternative
            let! implementation =
                match state.Graph.Nodes.TryFind carrier.Implementation with
                | Some implementation -> preturn implementation
                | None -> fail (Message "Callable aggregate alternative has no published implementation declaration.")
            let! alternativeShape =
                match Operands.project ctx alternative.Carrier with
                | Result.Ok shape -> preturn shape
                | Result.Error reason -> fail (Message reason)
            do! ensure (Operands.functionType shape = Operands.functionType alternativeShape &&
                        Operands.environmentType shape = Operands.environmentType alternativeShape)
                    "Callable aggregate selection has no source-settled common code and environment convention."
            let name = Values.aggregateComponent occurrence row.Slot alternative.Ordinal
            let code = { SSA = name 14; Type = Operands.functionType shape }
            let symbol = Alex.CodeGeneration.CallableSymbols.lambda state.Graph implementation false
            let! constant = pFuncConstant code.SSA symbol code.Type
            let! environment =
                match alternative.EnvironmentPlacement, Operands.environmentType shape with
                | None, None -> preturn None
                | Some placement, Some ty when ty = TMemRefStatic(placement.ViewBytes, TInt(IntWidth 8)) -> parser {
                    let value = { SSA = name 15; Type = ty }
                    let! loads = pTypedExtractView value.SSA storage.SSA placement.ByteOffset (name 16) (name 17) (name 18) ty storage.Type
                    return Some(loads, value)
                  }
                | _ -> fail (Message "Callable aggregate read lost its paired environment view.")
            return alternative.Ordinal, [constant], code, environment
        }) |> Alex.XParsec.Extensions.sequence
    let! codeOps, code = pSelect row 20 selectorValue (arms |> List.map (fun (ordinal, ops, code, _) -> ordinal, ops, code))
    let! environmentOps, environment =
        match Operands.environmentType shape with
        | None -> preturn ([], None)
        | Some _ -> parser {
            let! environments =
                arms |> List.map (fun (ordinal, _, _, environment) ->
                    match environment with
                    | Some(ops, value) -> preturn (ordinal, ops, value)
                    | None -> fail (Message "Callable aggregate selection dropped a required environment arm."))
                |> Alex.XParsec.Extensions.sequence
            let! ops, value = pSelect row 30 selectorValue environments
            return ops, Some value
          }
    let! result =
        match Operands.create shape code environment with
        | Result.Ok result -> preturn result
        | Result.Error reason -> fail (Message reason)
    return storageOps @ selectorOps @ codeOps @ environmentOps, TRCallable result
}
