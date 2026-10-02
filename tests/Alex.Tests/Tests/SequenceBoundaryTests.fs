module Alex.Tests.SequenceBoundaryTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

/// An owner with its typed generator formal, but no suspension segments,
/// frame or resumption construction. A delimiter adds ownership only.
let private fixture delegated owned =
    // The revision states the six nodes and the edge set the fixture declares. An owned
    // fixture also states the origin of the constructor, which is how a revision holds
    // ownership. It states no frame, no segment and no Emission row.
    let sequenceType = sequenceOf boolType
    let formalType = pointerTo sequenceType
    let payload = node 0 (SemanticKind.PatternBinding "input") (if delegated then sequenceType else boolType) [] (Some 1)
    let site = node 1 (if delegated then SemanticKind.YieldBang payload.Id else SemanticKind.Yield payload.Id)
                    unitType [0] (Some 3)
    let formal = node 2 (SemanticKind.PatternBinding "_seq_ptr") formalType [] (Some 3)
    let generator =
        node 3 (SemanticKind.Lambda(["_seq_ptr", formalType, formal.Id], site.Id, [], None, LambdaContext.SeqGenerator))
             (functionFrom formalType boolType) [2; 1] (Some 4)
    let owner = node 4 (SemanticKind.SeqExpr(generator.Id, [])) sequenceType [3] (Some 5)
    let binding = node 5 (SemanticKind.Binding("values", false, false, None)) sequenceType [4] None
    let edges : Hyperedge list =
        if owned then
            [{ Sources = [owner.Id; generator.Id]; Target = site.Id
               Class = EdgeClass.Suspension; Role = EdgeRole.Delimiter; Ordinal = 0 }]
        else []
    let raw = revision [payload; site; formal; generator; owner; binding]
    let origins = if owned then Map.ofList [owner.Id, owner.Id] else Map.empty
    let graph =
        { raw with Edges = edges; Codata = { raw.Codata with SequenceOrigins = origins } }
        |> declareTraversalReadings
    let position = Zipper.create graph binding.Id |> require "Missing sequence binding" |> atChild owner.Id
    position, generator.Id, site.Id, payload.Id

let private observe (position: Zipper.PSGZipper) =
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode position.Focus.Id (Arg 0) (TInt(IntWidth 1)) operands
    let nodes, types = operands.NodeAssoc, operands.SSATypes
    let rootScope = ref (ScopeContext.root ())
    let scope = ref (ScopeContext.createChild rootScope.Value FunctionLevel)
    let originalRoot, originalScope = rootScope.Value, scope.Value
    let visited = ref Set.empty
    let ctx: WitnessContext =
        { Coeffects = coeffects 64
          Accumulator = operands; RootAccumulator = operands
          ScopeContext = scope; RootScopeContext = rootScope
          Graph = position.Graph; Zipper = position
          GlobalVisited = visited; TraversalVisited = visited }
    let output = Alex.Witnesses.SeqWitness.nanopass.Witness ctx position.Focus
    Assert.Empty(output.InlineOps)
    Assert.Empty(output.TopLevelOps)
    Assert.Same(position.Graph, ctx.Graph)
    Assert.Same(position.Graph.Nodes, ctx.Graph.Nodes)
    Assert.Same(position.Graph.Edges, ctx.Graph.Edges)
    Assert.Same(position, ctx.Zipper)
    Assert.Same(position.Path, ctx.Zipper.Path)
    Assert.Same(nodes, operands.NodeAssoc)
    Assert.Same(types, operands.SSATypes)
    Assert.Same(originalRoot, rootScope.Value)
    Assert.Same(originalScope, scope.Value)
    Assert.Empty(visited.Value)
    Assert.Empty(operands.AllOps)
    Assert.Empty(operands.Errors)
    Assert.Empty(operands.EmittedGlobals)
    Assert.Empty(operands.EmittedStaticGlobals)
    Assert.Empty(operands.PendingStaticGlobals)
    output.Result

[<Theory>]
[<InlineData("SeqExpr", false)>]
[<InlineData("SeqExpr", true)>]
[<InlineData("Yield", false)>]
[<InlineData("Yield", true)>]
[<InlineData("YieldBang", false)>]
[<InlineData("YieldBang", true)>]
let ``suspension boundaries require more than owner identity`` kind owned =
    let owner, generator, site, _ = fixture (kind = "YieldBang") owned
    if owned then
        let edge = Assert.Single owner.Graph.Edges
        Assert.Equal<NodeId list>([owner.Focus.Id; generator], edge.Sources)
        Assert.Equal(site, edge.Target)
    let position = if kind = "SeqExpr" then owner else owner |> atChild generator |> atChild site
    Assert.NotEmpty(position.Path)
    match observe position with
    | TRError diagnostic when kind = "SeqExpr" && not owned ->
        // A constructor with no origin is refused for the origin, before its frame is sought.
        Assert.Equal(sprintf "Baker sequence settlement did not settle the constructor origin for SeqExpr node %d" (NodeId.value owner.Focus.Id), diagnostic.Message)
    | TRError diagnostic ->
        Assert.Equal(kind + " requires Baker-settled suspension segments, frame and resumption; delimiter ownership alone is insufficient", diagnostic.Message)
    | result -> failwithf "Unelaborated suspension was accepted: %A" result

[<Fact>]
let ``unrelated node remains available to other witnesses`` () =
    let owner, generator, site, payload = fixture false true
    let position = owner |> atChild generator |> atChild site |> atChild payload
    match observe position with
    | TRSkip -> ()
    | result -> failwithf "Sequence witness consumed an unrelated node: %A" result
