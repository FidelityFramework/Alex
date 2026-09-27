module Alex.Tests.ZipperTests

open Xunit
open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.XParsec.PSGCombinators
open Alex.Tests.Build
open Alex.Tests.ArrayRead
module Zipper = Alex.Traversal.PSGZipper

[<Fact>]
let ``sibling round trip preserves the enclosing scope and settled graph facts`` () =
    let fixture = arrayRead true
    let atIndex = fixture.Position |> atChild fixture.Index
    let atArray = Zipper.left atIndex |> require "No preceding array operand"
    let roundTrip = Zipper.right atArray |> require "No following index operand"
    Assert.Equal(fixture.Index, roundTrip.Focus.Id)
    Assert.Equal(fixture.Lambda, (Zipper.findEnclosingLambda roundTrip |> require "Lost lambda scope").Id)
    Assert.Equal(fixture.Call, (Zipper.up roundTrip |> require "Lost call context").Focus.Id)
    Assert.Same(fixture.Graph, roundTrip.Graph)
    Assert.Same(fixture.Graph.Nodes[fixture.Index], roundTrip.Focus)
    Assert.Same(fixture.Graph.Codata, roundTrip.Graph.Codata)
    Assert.Same(fixture.Graph.Edges, roundTrip.Graph.Edges)
    Assert.Equal(Some(ValueRange.Bounded(128I, 255I)), roundTrip.Focus.ValueRange)
    let proofEdge = Assert.Single(roundTrip.Graph.Edges)
    Assert.Equal<NodeId list>([fixture.Index], proofEdge.Sources)
    Assert.Equal(fixture.Proof, proofEdge.Target)
    Assert.Equal(EdgeRole.Constrains, proofEdge.Role)

[<Fact>]
let ``one shared node retains a distinct enclosing lambda at each Huet position`` () =
    let shared = node 0 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let makeLambda number name =
        node number (SemanticKind.Lambda([], shared.Id, [], Some name, LambdaContext.RegularClosure))
            (functionFrom unitType boolType) [0] None
    let first, second = makeLambda 1 "first", makeLambda 2 "second"
    let root = node 3 (SemanticKind.Sequential [first.Id; second.Id]) second.Type [1; 2] None
    let graph = revision [shared; first; second; root]
    let start = Zipper.create graph root.Id |> require "Missing root"
    let leftUse = start |> atChild first.Id |> atChild shared.Id
    let rightUse = start |> atChild second.Id |> atChild shared.Id
    Assert.Same(leftUse.Focus, rightUse.Focus)
    Assert.Equal(first.Id, (Zipper.findEnclosingLambda leftUse |> require "Missing first scope").Id)
    Assert.Equal(second.Id, (Zipper.findEnclosingLambda rightUse |> require "Missing second scope").Id)
    Assert.Same(graph, leftUse.Graph)
    Assert.Same(graph, rightUse.Graph)
    let reRooted = Zipper.focusOn shared.Id rightUse |> require "Cannot re-root"
    Assert.True(Zipper.isAtRoot reRooted)
    Assert.True((Zipper.findEnclosingLambda reRooted).IsNone)

[<Fact>]
let ``binding-name parser reads the zipper parent and restores its focus`` () =
    let fixture = arrayRead true
    let lambda = Zipper.up fixture.Position |> require "Missing lambda"
    let operands = MLIRAccumulator.empty ()
    // Composing another observation after pLambdaWithBinding detects leaked parser focus.
    let observation = XParsec.Combinators.parser {
        let! name, _, body, _ = pLambdaWithBinding
        let! current = getCurrentNode
        return name, body, current.Id
    }
    match matchAt observation lambda 64 operands with
    | Result.Ok ((name, body, current), position) ->
        Assert.Equal("read", name)
        Assert.Equal(fixture.Call, body)
        Assert.Equal(fixture.Lambda, current)
        Assert.Equal(fixture.Lambda, position.Focus.Id)
        Assert.Same(fixture.Graph, position.Graph)
        Assert.Empty(operands.AllOps)
    | Result.Error message -> failwith message

[<Fact>]
let ``invalid navigation does not manufacture a scope or graph node`` () =
    let fixture = arrayRead true
    let root = Zipper.create fixture.Graph fixture.Binding |> require "Missing root"
    Assert.True((Zipper.up root).IsNone)
    Assert.True((Zipper.left root).IsNone)
    Assert.True((Zipper.right root).IsNone)
    Assert.True((Zipper.down -1 root).IsNone)
    Assert.True((Zipper.down root.Focus.Children.Length root).IsNone)
    // One number past the greatest the revision holds. The revision holds no such node.
    let absent = NodeId (1 + (fixture.Graph.Nodes |> Map.toList |> List.map (fst >> NodeId.value) |> List.max))
    Assert.True((Zipper.create fixture.Graph absent).IsNone)
    Assert.True((Zipper.focusOn absent fixture.Position).IsNone)
    let error = Assert.ThrowsAny<System.Exception>(fun () -> Zipper.requireNode absent fixture.Position |> ignore)
    Assert.Contains("not found in graph", error.Message)
    Assert.Same(fixture.Graph, fixture.Position.Graph)
