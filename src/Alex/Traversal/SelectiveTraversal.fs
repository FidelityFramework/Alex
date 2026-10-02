/// Selective witnessing of Baker's published regions. Region membership,
/// fingerprints and dependency edges are observations, never discovered here.
module Alex.Traversal.SelectiveTraversal

open Fidelity.PSG
open Alex.Correspondence
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Traversal.PSGZipper
open Alex.Traversal.MLIRTransfer

type private HeldRegion = {
    Fingerprint: string
    Dependencies: Set<string>
    Operation: MLIROp
}

/// Only a successful selective transfer can create retained operation state.
/// No old graph, node, occurrence, operand map or proof receipt is retained.
[<NoEquality; NoComparison>]
type State = private {
    Coeffects: TransferCoeffects
    Fingerprints: Map<string, string>
    Held: Map<string, HeldRegion>
}

type Statistics = {
    Changed: string list
    Retained: string list
    Retired: string list
    WitnessedNodes: Map<string, int>
}

[<NoEquality; NoComparison>]
type RegionOutput = {
    Region: WitnessRegion
    Operations: MLIROp list
    Definitions: EmittedDefinition list
    Reused: bool
}

[<NoEquality; NoComparison>]
type Output = {
    Scope: SemanticScope
    Operations: MLIROp list
    Definitions: EmittedDefinition list
    Regions: RegionOutput list
    State: State
    Statistics: Statistics
}

let private collect results =
    List.foldBack (fun item rest ->
        item |> Result.bind (fun value -> rest |> Result.map (fun values -> value :: values))) results (Ok [])

let private refusal reason = Result.Error { Reason = reason; Witnessed = [] }

/// Rebind an authorized occurrence to this revision. A stale/truncated path is
/// a refusal, rather than a request to reconstruct source incidence.
let private occurrence scope (region: WitnessRegion) =
    let graph = graph scope
    let node id =
        match graph.Nodes.TryFind id with
        | Some current -> Ok current
        | None -> Result.Error (sprintf "Region '%s' names absent node %A" region.Identity id)
    match region.Root, region.Anchor with
    | Some root, Some anchor ->
        node root |> Result.bind (fun focus ->
            let held = { Scope = scope; Focus = focus; Anchor = anchor; Path = region.Path }
            validateOccurrence scope held |> Result.map (fun () -> held))
    | _ -> Result.Error (sprintf "Scalar region '%s' lacks its root or anchor occurrence" region.Identity)

let private validateManifest (revision: Revision) (segmentation: WitnessSegmentation) =
    let regions = segmentation.Regions
    let identities = regions |> List.map _.Identity |> Set.ofList
    let nodeIds = revision.Nodes.Keys |> Set.ofSeq
    let common = regions |> List.filter (fun region -> region.Flavor = WitnessRegionKind.Common)
    let membership = regions |> List.collect (fun region -> region.Members |> Set.toList)
    if segmentation.Version <> 1 then Result.Error "Unsupported published witness segmentation version"
    elif identities.Count <> regions.Length then Result.Error "Published witness segmentation has duplicate region identities"
    elif regions |> List.exists (fun region -> System.String.IsNullOrWhiteSpace region.Identity || System.String.IsNullOrWhiteSpace region.Fingerprint) then
        Result.Error "Published witness segmentation has an empty identity or fingerprint"
    elif common.Length <> 1 then Result.Error "Published witness segmentation must have exactly one common region"
    elif membership.Length <> (Set.ofList membership).Count then Result.Error "Published witness segmentation has overlapping members"
    elif Set.ofList membership <> nodeIds then Result.Error "Published witness segmentation does not exactly cover the current graph"
    elif regions |> List.exists (fun region -> not (Set.isSubset region.Dependencies identities)) then
        Result.Error "Published witness segmentation has absent dependency identities"
    elif regions |> List.exists (fun region ->
        match region.OwnerSupport with
        | SupportKey.WholeOwningAnalysisRegion identity -> System.String.IsNullOrWhiteSpace identity
        | _ -> true) then
        Result.Error "Published witness segmentation lacks its source owning-analysis support account"
    elif common |> List.exists (fun region -> region.Root.IsSome || region.Anchor.IsSome || not region.Path.IsEmpty) then
        Result.Error "Published common witness region must not claim a scalar occurrence"
    elif regions |> List.exists (fun region ->
        region.Flavor = WitnessRegionKind.ScalarCallable &&
        (region.Root |> Option.forall (fun root -> not (region.Members.Contains root)))) then
        Result.Error "Published scalar witness region does not contain its root"
    else Ok ()

/// This initial cohort retains ordinary scalar computation only. In particular,
/// no operation carrying a source storage/boundary/spatial authority survives.
let rec private scalarBody operations =
    operations |> List.forall (function
        | ArithOp _ | IndexOp _ | Assert _ -> true
        | FuncOp(Return _) | FuncOp(FuncCall _) -> true
        | Block(_, body) | Region body -> scalarBody body
        | SCFOp(If(_, yes, no, _)) -> scalarBody yes && Option.forall scalarBody no
        | SCFOp(IndexSwitch(_, cases, fallback, _)) -> List.forall (snd >> scalarBody) cases && scalarBody fallback
        | SCFOp(While(condition, body)) -> scalarBody condition && scalarBody body
        | SCFOp(For(_, _, _, _, body)) -> scalarBody body
        | SCFOp(Yield _) | SCFOp(Condition _) -> true
        | _ -> false)

let private retainable = function
    | FuncOp(FuncDef(_, _, _, body, _))
    | NoUnwindFunction(FuncDef(_, _, _, body, _)) -> scalarBody body
    | _ -> false

let private errors (accumulator: MLIRAccumulator) =
    match accumulator.Errors with
    | [] -> Ok ()
    | failures -> Result.Error (failures |> List.map Diagnostic.format |> String.concat "\n")

let private freshScalar registry revision coeffects scope (region: WitnessRegion) =
    occurrence scope region |> Result.bind (fun at ->
        let accumulator = MLIRAccumulator.empty ()
        accumulator.WitnessScope <- Some scope
        let root = ref (ScopeContext.root ())
        let visited = ref Set.empty
        let zipper =
            { Graph = revision; Focus = at.Focus; Path = at.Path }
        let context =
            { Graph = revision; Coeffects = coeffects; Accumulator = accumulator; RootAccumulator = accumulator
              ScopeContext = root; RootScopeContext = root; Zipper = zipper
              GlobalVisited = visited; TraversalVisited = visited }
        visitAllNodes (combineWitnesses registry.Nanopasses) context at.Focus visited
        let coverage = CoverageValidation.validateRegionCoverage revision region.Members visited.Value
        let operations = ScopeContext.getOps root.Value
        errors accumulator |> Result.bind (fun () ->
            if not (Set.isSubset visited.Value region.Members) then
                Result.Error (sprintf "Witness of region '%s' escaped its published members" region.Identity)
            elif not coverage.IsEmpty then Result.Error (coverage |> List.map Diagnostic.format |> String.concat "\n")
            else
                match operations, List.rev accumulator.EmittedDefinitions with
                | [operation], [definition] when retainable operation &&
                      obj.ReferenceEquals(definition.Operation, operation) &&
                      definition.Occurrence.Focus.Id = at.Focus.Id &&
                      definition.Occurrence.Path = region.Path ->
                    Ok ({ Region = region; Operations = operations; Definitions = [definition]; Reused = false }, visited.Value.Count)
                | _ -> Result.Error (sprintf "Scalar region '%s' did not witness exactly one source-independent function definition" region.Identity)))

let private freshCommon registry revision coeffects scope scalarMembers (region: WitnessRegion) =
    let accumulator = MLIRAccumulator.empty ()
    accumulator.WitnessScope <- Some scope
    let root = ref (ScopeContext.root ())
    // These nodes are covered by the separate, checked scalar results. Starting
    // with their set prevents entering retained bodies at all.
    let visited = ref scalarMembers
    runAllNanopasses registry.Nanopasses revision coeffects accumulator root visited
    let actual = Set.difference visited.Value scalarMembers
    let coverage =
        CoverageValidation.validateRegionCoverage revision region.Members actual @
        CoverageValidation.validateBoundaryCoverage revision accumulator.BoundaryScopes
    errors accumulator |> Result.bind (fun () ->
        if not coverage.IsEmpty then Result.Error (coverage |> List.map Diagnostic.format |> String.concat "\n")
        elif not (Set.isSubset actual region.Members) then Result.Error "Common witness escaped its published region"
        else Ok ({ Region = region; Operations = ScopeContext.getOps root.Value
                   Definitions = List.rev accumulator.EmittedDefinitions; Reused = false }, actual.Count))

/// The registry parameter makes the traversal contract testable with contract
/// values. Production supplies its ordinary target registry, unchanged.
let internal transferWithRegistry registry revision coeffects (prior: State option) : Result<Output, TransferRefusal> =
    match revision.Codata.WitnessSegmentation with
    | None -> refusal "Revision lacks Baker's published witness segmentation"
    | Some segmentation ->
        validateManifest revision segmentation |> Result.mapError (fun reason -> { Reason = reason; Witnessed = [] })
        |> Result.bind (fun () ->
            if registry.Nanopasses.IsEmpty then refusal "Alex witness registry is empty for selective witnessing"
            else
                let scope = beginWholeGraphWitness revision
                let fingerprints = segmentation.Regions |> List.map (fun region -> region.Identity, region.Fingerprint) |> Map.ofList
                let compatible = prior |> Option.filter (fun held -> held.Coeffects = coeffects)
                let initiallyChanged =
                    segmentation.Regions |> List.filter (fun region ->
                        match compatible |> Option.bind (fun held -> held.Fingerprints.TryFind region.Identity),
                              compatible |> Option.bind (fun held -> held.Held.TryFind region.Identity) with
                        | Some fingerprint, _ when region.Flavor = WitnessRegionKind.Common && fingerprint = region.Fingerprint -> false
                        | Some fingerprint, Some held when fingerprint = region.Fingerprint && held.Dependencies = region.Dependencies -> false
                        | _ -> true)
                    |> List.map _.Identity |> Set.ofList
                let rec dependentClosure changed =
                    let next = segmentation.Regions |> List.fold (fun dirty region ->
                        if not (Set.intersect region.Dependencies dirty).IsEmpty then dirty.Add region.Identity else dirty) changed
                    if next = changed then changed else dependentClosure next
                let changed = dependentClosure initiallyChanged
                let scalars = segmentation.Regions |> List.filter (fun region -> region.Flavor = WitnessRegionKind.ScalarCallable)
                let scalarResults =
                    scalars |> List.map (fun region ->
                        match compatible |> Option.bind (fun state -> state.Held.TryFind region.Identity) with
                        | Some held when not (changed.Contains region.Identity) ->
                            occurrence scope region |> Result.map (fun at ->
                                { Region = region; Operations = [held.Operation]
                                  Definitions = [{ Operation = held.Operation; Occurrence = at }]; Reused = true }, 0)
                        | _ -> freshScalar registry revision coeffects scope region)
                    |> collect
                scalarResults |> Result.bind (fun scalarResults ->
                    let scalarMembers = scalars |> List.map _.Members |> Set.unionMany
                    let common = segmentation.Regions |> List.find (fun region -> region.Flavor = WitnessRegionKind.Common)
                    freshCommon registry revision coeffects scope scalarMembers common
                    |> Result.map (fun commonResult ->
                        let results = scalarResults @ [commonResult]
                        let regions = results |> List.map fst
                        let held =
                            scalarResults |> List.map (fun (output, _) ->
                                output.Region.Identity,
                                { Fingerprint = output.Region.Fingerprint; Dependencies = output.Region.Dependencies
                                  Operation = List.exactlyOne output.Operations }) |> Map.ofList
                        { Scope = scope; Operations = regions |> List.collect _.Operations
                          Definitions = regions |> List.collect _.Definitions; Regions = regions
                          State = { Coeffects = coeffects; Fingerprints = fingerprints; Held = held }
                          Statistics =
                            { Changed = regions |> List.filter (fun output -> not output.Reused) |> List.map _.Region.Identity
                              Retained = regions |> List.filter _.Reused |> List.map _.Region.Identity
                              Retired = prior |> Option.map (fun state -> Set.difference (state.Fingerprints.Keys |> Set.ofSeq) (fingerprints.Keys |> Set.ofSeq) |> Set.toList) |> Option.defaultValue []
                              WitnessedNodes = results |> List.map (fun (output, count) -> output.Region.Identity, count) |> Map.ofList } }))
                |> Result.mapError (fun reason -> { Reason = reason; Witnessed = [] }))

let internal transfer revision coeffects prior =
    transferWithRegistry (WitnessRegistry.createRegistry coeffects.TargetPlatform) revision coeffects prior
