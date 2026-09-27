/// Witness source-published boundary calls through Patterns and Elements.
/// Host/library selection, declarations, ABI and adaptation are source facts.
module Alex.Witnesses.PlatformWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.PlatformPatterns


let private witnessPlatform (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    let boundary = ctx.Graph.Emission.Boundary
    let pattern =
        if boundary.Calls.ContainsKey node.Id then Some pBoundaryCall
        elif boundary.ByteViews.ContainsKey node.Id then Some pPublishedByteView
        elif boundary.IntrinsicWrites.ContainsKey node.Id then Some pIntrinsicWrite
        elif boundary.DeclarationLeaves.Contains node.Id then Some pBoundaryDeclaration
        else None
    match pattern with
    | Some pattern ->
        match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Result.Ok ((operations, result), _) ->
            { InlineOps = operations; TopLevelOps = []; Result = result }
        | Result.Error reason -> WitnessOutput.error reason
    | None ->
        let callable = ctx.Graph.Emission.Callable
        if callable.ForeignCalls.Contains node.Id then
            WitnessOutput.error $"Boundary call {NodeId.value node.Id} lacks its source-published declaration and ABI contract."
        else WitnessOutput.skip

let nanopass : Nanopass = { Name = "Platform"; Witness = witnessPlatform }
