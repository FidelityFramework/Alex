/// Passive observation of the async formation, activation and orchestration
/// occurrences the revision names in Codata.AsyncFormations, Codata.AsyncActivations
/// and Codata.AsyncOrchestrations. The occurrence is selected by its published
/// row, never by an intrinsic name.
///
/// An orchestration row publishes the result capacity, the element stride and
/// the child activations. Its result storage must have a published memory
/// allocation operation; that operation's witness emits the settled residence
/// and element carrier.
module Alex.Witnesses.AsyncWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.AsyncPatterns

let private refuse (node: SemanticNode) phase message =
    WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "Async") (Some phase) message

let private observe (ctx: WitnessContext) (node: SemanticNode) phase pattern =
    match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
    | Result.Ok ((operations, result), _) -> { InlineOps = operations; TopLevelOps = []; Result = result }
    | Result.Error reason -> refuse node phase reason

let private orchestration (ctx: WitnessContext) (node: SemanticNode) (row: AsyncOrchestration) =
    match ctx.Graph.Emission.Memory.Operations.TryFind row.ResultStorage with
    | Some(MemoryWitnessOperation.ArrayAllocation allocation) when allocation.Site=row.ResultStorage -> WitnessOutput.skip
    | _ ->
        let site = NodeId.value node.Id
        refuse node "orchestration result storage"
            (sprintf "Async orchestration %d: Codata.AsyncOrchestrations publishes a result capacity of %d elements at a stride of %d bytes for %d child activations, and the revision publishes no storage operation for the result array (no Emission.Memory.Operations row at node %d). Alex does not choose a residence or an element carrier for orchestration result storage."
                site row.ResultCapacity row.ElementStride row.Children.Length (NodeId.value row.ResultStorage))

let private witness (ctx: WitnessContext) (node: SemanticNode) =
    let codata = ctx.Graph.Codata
    match codata.AsyncFormations.TryFind node.Id, codata.AsyncActivations.TryFind node.Id, codata.AsyncOrchestrations.TryFind node.Id with
    | Some formation, None, None -> observe ctx node "formation" (pAsyncFormation ctx formation)
    | None, Some activation, None -> observe ctx node "activation" (pAsyncActivation ctx activation)
    | None, None, Some row -> orchestration ctx node row
    | None, None, None -> WitnessOutput.skip
    | _ ->
        refuse node "published rows"
            (sprintf "Node %d is published under more than one of Codata.AsyncFormations, Codata.AsyncActivations and Codata.AsyncOrchestrations." (NodeId.value node.Id))

let nanopass : Nanopass = { Name = "Async"; Witness = witness }
