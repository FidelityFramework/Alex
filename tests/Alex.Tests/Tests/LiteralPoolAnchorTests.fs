module Alex.Tests.LiteralPoolAnchorTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.ScopeContext
open Alex.Tests.Build

let private anchors =
    [ "layout_user_strings"; "storage_a"; "view_a"; "sentinel_a"; "storage_b"; "view_b"; "sentinel_b" ]

/// This component fixture states the source-owned pool and complete allocation
/// obligation inventory the literal witness reads. Another live scope owns
/// literal 2; its identity remains in the shared pool, but its body is absent
/// here. This tests the witness reading, not legacy whole-Revision integrity or
/// proof discharge; the source producer's inventory is checked in Clef tests.
let private fixture otherBody (publishedAnchors: string list) =
    let first =
        { node 1 (SemanticKind.Literal(NativeLiteral.String "a")) stringType [] None with
            ObligationAnchors = [ "layout_user_strings"; "storage_a"; "view_a"; "sentinel_a" ] }
    let second =
        { node 2 (SemanticKind.Literal(NativeLiteral.String "b")) stringType [] None with
            ObligationAnchors = [ "layout_user_strings"; "storage_b"; "view_b"; "sentinel_b" ] }
    let pool : StaticStringPool =
        { Symbol = "source_pool"; Bytes = [ 97uy; 0uy; 98uy; 0uy ]; Alignment = 1; Size = 4; UsedSize = 4
          Entries =
            [ { NodeIds = [first.Id]; Content = "a"; Offset = 0; Length = 1; StorageLength = 2 }
              { NodeIds = [second.Id]; Content = "b"; Offset = 2; Length = 1; StorageLength = 2 } ]
          SpaceName = "rodata"; Capacity = 4096L; SpaceAlignment = 1; Granularity = 1; DeclarationNode = NodeId 90 }
    let graph = revision (if otherBody then [first; second] else [first])
    let graph =
        { graph with StaticStringPool = Some pool
                     Emission = { graph.Emission with Storage = { graph.Emission.Storage with LiteralPoolAnchors = publishedAnchors } } }
        |> declareTraversalReadings
    let position = focus graph first
    let accumulator = MLIRAccumulator.empty ()
    let scope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    let context : WitnessContext =
        { Graph = graph; Zipper = position; Coeffects = coeffects 64
          Accumulator = accumulator; RootAccumulator = accumulator
          ScopeContext = scope; RootScopeContext = scope
          GlobalVisited = visited; TraversalVisited = visited }
    graph, first, context, accumulator, pool

[<Fact>]
let ``pool allocation reads its complete source inventory without other literal bodies`` () =
    let graph, first, context, accumulator, pool = fixture false anchors
    Assert.False(graph.Nodes.ContainsKey(NodeId 2))
    let output = Alex.Witnesses.LiteralWitness.nanopass.Witness context first
    match output.Result with
    | TRValue _ -> ()
    | other -> failwithf "A complete source pool inventory was refused: %A" other
    Assert.Equal(4, output.InlineOps.Length)
    match Assert.Single output.TopLevelOps with
    | MLIROp.GlobalBytePool(name, bytes, alignment, observed) ->
        Assert.Equal(pool.Symbol, name)
        Assert.Equal<byte list>(pool.Bytes, bytes)
        Assert.Equal(pool.Alignment, alignment)
        Assert.Equal<string list>(anchors, observed)
    | other -> failwithf "Expected the source pool allocation, got %A" other
    Assert.True(accumulator.EmittedGlobals.Contains pool.Symbol)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``a missing authoritative pool inventory refuses before allocation or operands`` otherBody =
    let _, first, context, accumulator, pool = fixture otherBody []
    let output = Alex.Witnesses.LiteralWitness.nanopass.Witness context first
    match output.Result with
    | TRError diagnostic ->
        Assert.Contains("source-owned allocation obligation inventory", diagnostic.Message)
        Assert.Equal(Some first.Id, diagnostic.NodeId)
    | other -> failwithf "Missing pool inventory was witnessed: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Empty accumulator.AllOps
    Assert.False(accumulator.EmittedGlobals.Contains pool.Symbol)
    Assert.True((MLIRAccumulator.recallNode first.Id accumulator).IsNone)

[<Fact>]
let ``layout anchor alone does not substitute for the complete allocation inventory`` () =
    let _, first, context, accumulator, pool = fixture false [ "layout_user_strings" ]
    let output = Alex.Witnesses.LiteralWitness.nanopass.Witness context first
    match output.Result with
    | TRError diagnostic -> Assert.Contains("source-owned allocation obligation inventory", diagnostic.Message)
    | other -> failwithf "Partial pool inventory was witnessed: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.False(accumulator.EmittedGlobals.Contains pool.Symbol)

[<Fact>]
let ``an explicitly unanchored component inventory does not invent obligations`` () =
    // This component-only row has no source obligations. Actual source pool
    // admission is tested separately; the witness does not synthesize a proof.
    let graph, first, _, _, _ = fixture false []
    let first = { first with ObligationAnchors = [] }
    let graph = { graph with Nodes = graph.Nodes.Add(first.Id, first) }
    let position = focus graph first
    let accumulator = MLIRAccumulator.empty ()
    let scope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    let context : WitnessContext =
        { Graph = graph; Zipper = position; Coeffects = coeffects 64
          Accumulator = accumulator; RootAccumulator = accumulator
          ScopeContext = scope; RootScopeContext = scope
          GlobalVisited = visited; TraversalVisited = visited }
    let output = Alex.Witnesses.LiteralWitness.nanopass.Witness context first
    match Assert.Single output.TopLevelOps with
    | MLIROp.GlobalBytePool(_, _, _, observed) -> Assert.Empty observed
    | other -> failwithf "Expected the unanchored component allocation, got %A" other
