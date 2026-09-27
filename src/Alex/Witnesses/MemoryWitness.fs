/// Witness the memory operation published for the current Huet occurrence.
/// Baker owns its operands, representation, access and storage authority.
module Alex.Witnesses.MemoryWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.MemoryPatterns


let private witnessMemory (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    let memory = ctx.Graph.Emission.Memory
    if memory.Operations.ContainsKey node.Id then
        match tryMatchWithDiagnostics pPublishedMemoryOperation ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Result.Ok ((operations, declarations, result), _) ->
            { InlineOps = operations; TopLevelOps = declarations; Result = result }
        | Result.Error reason -> WitnessOutput.error reason
    elif memory.Required.Contains node.Id then
        WitnessOutput.error $"Memory operation {NodeId.value node.Id} lacks its source-published access and representation contract."
    else WitnessOutput.skip

let nanopass : Nanopass = { Name = "Memory"; Witness = witnessMemory }
