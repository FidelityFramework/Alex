/// Passive observation of the async formation and activation occurrences the
/// revision names in Codata.AsyncFormations and Codata.AsyncActivations. The
/// occurrence is selected by its published row, never by an intrinsic name.
module Alex.Witnesses.AsyncWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.AsyncPatterns

let private observe (ctx: WitnessContext) (node: SemanticNode) phase pattern =
    match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
    | Result.Ok ((operations, result), _) -> { InlineOps = operations; TopLevelOps = []; Result = result }
    | Result.Error reason -> WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "Async") (Some phase) reason

let private witness (ctx: WitnessContext) (node: SemanticNode) =
    let codata = ctx.Graph.Codata
    match codata.AsyncFormations.TryFind node.Id, codata.AsyncActivations.TryFind node.Id with
    | Some formation, None -> observe ctx node "formation" (pAsyncFormation ctx formation)
    | None, Some activation -> observe ctx node "activation" (pAsyncActivation ctx activation)
    | Some _, Some _ ->
        WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "Async") (Some "published rows")
            (sprintf "Node %d is published as both an async formation and an async activation." (NodeId.value node.Id))
    | None, None -> WitnessOutput.skip

let nanopass : Nanopass = { Name = "Async"; Witness = witness }
