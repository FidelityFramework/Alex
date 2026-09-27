/// Alex witnesses share one post-order Huet traversal. This boundary returns
/// its operations and actual declaration occurrences before flattening loses
/// the source path; it does not schedule independent witness traversals.

module Alex.Traversal.MLIRTransfer

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.WitnessRegistry
open Alex.Traversal.NanopassArchitecture

/// A refused transfer keeps the operations witnessed before the refusal.
/// They are evidence for diagnosis and are never a module to compile.
type TransferRefusal = {
    Reason: string
    Witnessed: MLIROp list
}

/// Transfer one revision to MLIR operations.
///
/// 1. Build this transfer's target-selected witness registry
/// 2. Run every nanopass over one post-order traversal of the revision
/// 3. Return the operations with the occurrence of each emitted definition
///
/// Registered witnesses handle their categories at the current occurrence.
let transferWithCorrespondence
    (graph: Revision)
    (entryNodeId: NodeId)
    (coeffects: TransferCoeffects)
    : Result<MLIROp list * Alex.Correspondence.SemanticScope * Alex.Correspondence.EmittedDefinition list, TransferRefusal> =

    match Revision.tryNode entryNodeId graph with
    | None ->
        Result.Error { Reason = sprintf "Entry node %d not found" (NodeId.value entryNodeId); Witnessed = [] }
    | Some _ ->
        let registry = createRegistry coeffects.TargetPlatform
        let accumulator = executeNanopasses registry graph coeffects
        let operations = List.rev accumulator.AllOps
        match accumulator.Errors with
        | [] ->
            let scope = accumulator.WitnessScope |> Option.defaultWith (fun () -> Alex.Correspondence.beginWholeGraphWitness graph)
            Result.Ok (operations, scope, List.rev accumulator.EmittedDefinitions)
        | errors ->
            Result.Error { Reason = errors |> List.map Diagnostic.format |> String.concat "\n"; Witnessed = operations }

/// Entry for isolated transfer consumers. The production pipeline retains
/// correspondence through transferWithCorrespondence.
let transfer graph entryNodeId coeffects =
    transferWithCorrespondence graph entryNodeId coeffects
    |> Result.map (fun (operations, _, _) -> operations, [])
    |> Result.mapError (fun refusal -> refusal.Reason)
