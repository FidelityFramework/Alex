module Alex.Tests.SourceTraversalReadingsTests

open Xunit
open Fidelity.PSG
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

let private diamond () =
    let shared = node 4 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] (Some 99)
    let left = node 2 (SemanticKind.Sequential [shared.Id]) boolType [4] None
    let right = node 3 (SemanticKind.Sequential [shared.Id]) boolType [4] None
    let root = node 1 (SemanticKind.Sequential [left.Id; right.Id]) boolType [2; 3] None
    revision [root; left; right; shared] |> declareTraversalReadings

[<Fact>]
let ``declared source positions retain both actual shared occurrence paths independently of Parent metadata`` () =
    let graph = diamond ()
    let paths = graph.SourceReadings.Contexts[NodeId 4]
    Assert.Equal(2, paths.Length)
    Assert.Equal<Set<NodeId>>(Set.ofList [NodeId 2; NodeId 3], paths |> List.map (fun path -> path.Head.Parent) |> Set.ofList)
    Assert.All(paths, fun path ->
        Assert.Equal(2, path.Length)
        Assert.Equal<Result<NodeId, string>>(Ok(NodeId 1), RevisionNavigation.checkContext graph (NodeId 4) path))
    Assert.Equal(Some(NodeId 99), graph.Nodes[NodeId 4].Parent)

[<Theory>]
[<InlineData("missing-context")>]
[<InlineData("missing-port")>]
[<InlineData("stale-port")>]
[<InlineData("missing-position")>]
let ``missing or stale positional accounts refuse the actual declared occurrence`` defect =
    let graph = diamond ()
    let path = graph.SourceReadings.Contexts[NodeId 4].Head
    let frame = path.Head
    let readings = graph.SourceReadings
    let key = frame.Parent, frame.Port
    let changed =
        match defect with
        | "missing-context" -> { readings with Contexts = readings.Contexts.Remove(NodeId 4) }
        | "missing-port" -> { readings with Ports = readings.Ports.Remove key }
        | "stale-port" -> { readings with Ports = readings.Ports.Add(key, { readings.Ports[key] with Stamp = "different-source-port" }) }
        | _ -> { readings with Ports = readings.Ports.Add(key, { readings.Ports[key] with Positions = Map.empty }) }
    let graph = { graph with SourceReadings = changed }
    match RevisionNavigation.checkContext graph (NodeId 4) path with
    | Ok _ -> failwith "Missing or stale source position was accepted"
    | Error reason ->
        let expected =
            match defect with
            | "missing-context" -> "context inventory is absent"
            | "missing-port" -> "port account is absent"
            | "stale-port" -> "extent or stamp differs"
            | _ -> "absent from its declared original port position"
        Assert.Contains(expected, reason)

[<Fact>]
let ``a truncated occurrence path cannot manufacture an undeclared root`` () =
    let graph = diamond ()
    let inner = graph.SourceReadings.Contexts[NodeId 4].Head.Head
    let graph = { graph with SourceReadings =
        { graph.SourceReadings with Contexts = graph.SourceReadings.Contexts.Add(NodeId 4, [[inner]]) } }
    match RevisionNavigation.checkContext graph (NodeId 4) [inner] with
    | Ok _ -> failwith "A truncated source path manufactured a root"
    | Error reason -> Assert.Contains("root", reason)

[<Fact>]
let ``source omitted child refuses navigation without requiring its inactive body`` () =
    let dormant = { node 3 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None with IsReachable = false }
    let selected = node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let root = node 1 (SemanticKind.Sequential [selected.Id; dormant.Id]) boolType [2; 3] None
    let graph = revision [root; selected; dormant] |> declareTraversalReadings
    let graph = { graph with Nodes = graph.Nodes.Remove dormant.Id }
    Assert.False(graph.Nodes.ContainsKey dormant.Id)
    Assert.Equal<Result<NodeId, string>>(Ok selected.Id, RevisionNavigation.tryLocalChild graph root.Id 0)
    match RevisionNavigation.tryLocalChild graph root.Id 1 with
    | Error reason -> Assert.Contains("source omitted", reason)
    | other -> failwithf "Omitted child was not refused from its disposition: %A" other
    let position = Zipper.create graph root.Id |> require "Missing explicitly declared root"
    Assert.True((Zipper.down 0 position).IsSome)
    Assert.True((Zipper.down 1 position).IsNone)

[<Fact>]
let ``declaring a component graph never silently enriches the empty revision helper`` () =
    let graph = revision [node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None]
    Assert.Empty graph.SourceReadings.Contexts
    Assert.Empty graph.SourceReadings.Children
    Assert.Empty graph.SourceReadings.BindingUses
    Assert.Empty graph.CurrentClaims
