/// Snapshot-scoped correspondence between emitted definitions and the occurrences of
/// the revision they were witnessed at. Semantic scope comes from the published
/// revision; a backend partition is never authority to choose a source region.
module Alex.Correspondence

open System
open Fidelity.PSG
open Alex.Dialects.Core.Types

/// The current full-witness pipeline supplies one whole revision.
/// witnessRun distinguishes emission bookkeeping, not an accepted source
/// revision or temporal freshness.
[<NoEquality; NoComparison>]
type SemanticScope =
    | WholeCheckedGraph of witnessRun: Guid * graph: Revision

[<NoEquality; NoComparison>]
type Occurrence = {
    Scope: SemanticScope
    Focus: SemanticNode
    /// The actual traversal root captured with the path. Keeping it separate
    /// makes a truncated/re-rooted breadcrumb list observably different.
    Anchor: SemanticNode
    /// Actual Huet breadcrumbs, nearest parent first. Node.Parent is not used.
    Path: (SemanticNode * NodeId list * NodeId list) list
}

[<NoEquality; NoComparison>]
type EmittedDefinition = {
    Operation: MLIROp
    Occurrence: Occurrence
}

let witnessRun (WholeCheckedGraph(id, _)) = id
let graph (WholeCheckedGraph(_, graph)) = graph
let beginWholeGraphWitness graph = WholeCheckedGraph(Guid.NewGuid(), graph)

let sameScope left right =
    witnessRun left = witnessRun right && Object.ReferenceEquals(graph left, graph right)

let validateOccurrence scope (occurrence: Occurrence) =
    let nodes = (graph scope).Nodes
    let current (node: SemanticNode) =
        nodes.TryFind node.Id |> Option.exists (fun actual -> Object.ReferenceEquals(actual, node))
    let rec path (child: NodeId) (steps: (SemanticNode * NodeId list * NodeId list) list) =
        match steps with
        | [] -> child = occurrence.Anchor.Id
        | (parent, left, right) :: rest ->
            current parent && parent.Children = left @ [child] @ right && path parent.Id rest
    if not (sameScope scope occurrence.Scope) then Error "Witness occurrence belongs to a different checked graph snapshot or witness run"
    elif not (current occurrence.Anchor) || not (current occurrence.Focus) || not (path occurrence.Focus.Id occurrence.Path) then
        Error "Witness occurrence does not retain the actual current PSG focus and Huet path"
    else Ok ()

let definitionSymbol = function
    | MLIROp.SpatialModule(SpatialModuleWitness.Hardware plan) -> Some plan.Name
    | MLIROp.SpatialModule(SpatialModuleWitness.Kernel plan) -> Some plan.Name
    | MLIROp.FuncOp(FuncDef(name, _, _, _, _))
    | MLIROp.NoUnwindFunction(FuncDef(name, _, _, _, _))
    | MLIROp.GlobalString(name, _, _, _)
    | MLIROp.GlobalBytePool(name, _, _, _)
    | MLIROp.GlobalMemref(name, _, _)
    | MLIROp.GlobalArray(name, _, _)
    | MLIROp.HWOp(HWModule(name, _, _, _)) -> Some name
    | _ -> None

let isDefinition op = definitionSymbol op |> Option.isSome
let isOwnedOperation = function MLIROp.RawMLIR _ -> true | op -> isDefinition op
