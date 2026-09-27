module Alex.Witnesses.MappedViewWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.MappedViewPatterns

let private witness (ctx: WitnessContext) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Application _ when ctx.Graph.Foreign.MappedCalls.Contains node.Id ->
        match tryMatchWithDiagnostics pMappedCall ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
        | Result.Error message -> WitnessOutput.error message
    | _ -> WitnessOutput.skip

let nanopass : Nanopass = { Name = "MappedView"; Witness = witness }
