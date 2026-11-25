/// Snapshot-scoped correspondence between emitted definitions and the occurrences of
/// the revision they were witnessed at. Semantic scope comes from the published
/// revision; a backend partition is never authority to choose a source region.
module Alex.Correspondence

open Fidelity.PSG
open Alex.Dialects.Core.Types

/// The current full-witness pipeline supplies one whole published revision.
/// Scope identity is the exact published revision, not a process-global counter
/// or host observation label.
[<NoEquality; NoComparison>]
type SemanticScope =
    | WholeCheckedGraph of graph: Revision

[<NoEquality; NoComparison>]
type Occurrence = {
    Scope: SemanticScope
    Focus: SemanticNode
    /// The actual traversal root captured with the path. Keeping it separate
    /// makes a truncated/re-rooted breadcrumb list observably different.
    Anchor: NodeId
    /// Actual Huet breadcrumbs, nearest parent first. Node.Parent is not used.
    Path: OccurrenceBreadcrumb list
}

[<NoEquality; NoComparison>]
type EmittedDefinition = {
    Operation: MLIROp
    Occurrence: Occurrence
}

/// The actual result and typed operations returned by one successful witness.
/// This is physical emission evidence, not a source assignment or a naming rule.
[<NoEquality; NoComparison>]
type WitnessEmission<'result> = {
    Occurrence: Occurrence
    Result: 'result
    InlineOps: MLIROp list
    TopLevelOps: MLIROp list
}

let graph (WholeCheckedGraph graph) = graph
let beginWholeGraphWitness (graph: Revision) : SemanticScope = WholeCheckedGraph graph

let sameScope left right =
    graph left = graph right

let validateOccurrence scope (occurrence: Occurrence) =
    let nodes = (graph scope).Nodes
    let current (node: SemanticNode) =
        nodes.TryFind node.Id |> Option.exists (fun actual -> actual = node)
    if not (sameScope scope occurrence.Scope) then Error "Witness occurrence belongs to a different checked graph snapshot"
    elif not (current occurrence.Focus) then
        Error "Witness occurrence does not retain the actual current PSG focus and Huet path"
    else
        RevisionNavigation.checkContext (graph scope) occurrence.Focus.Id occurrence.Path
        |> Result.mapError (fun reason -> "Witness occurrence does not retain the actual current PSG focus and Huet path: " + reason)
        |> Result.bind (fun anchor ->
            if anchor = occurrence.Anchor then Ok ()
            else Error "Witness occurrence anchor differs from its whole source-authored path")

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
