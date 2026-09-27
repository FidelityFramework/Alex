/// Passive kernel declaration witnessing through the shared spatial Pattern.
module Alex.Witnesses.KernelModuleWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.SpatialPatterns

let private witnessKernel (_getCombinator: unit -> (WitnessContext -> SemanticNode -> WitnessOutput))
                          (ctx: WitnessContext) (node: SemanticNode) =
    let projection = ctx.Graph.Emission.Spatial
    if projection.Kernels.ContainsKey node.Id then
        match tryMatchWithDiagnostics pPublishedSpatialModule ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Result.Ok ((operations,result),_) -> { InlineOps=[]; TopLevelOps=operations; Result=result }
        | Result.Error reason -> WitnessOutput.error reason
    else
        match node.Kind with
        | SemanticKind.Binding(_,_,_,Some DeclRoot.KernelModule) -> WitnessOutput.error "Kernel declaration lacks its complete source spatial publication."
        | _ -> WitnessOutput.skip

let createNanopass getCombinator : Nanopass = { Name="KernelModule"; Witness=witnessKernel getCombinator }
