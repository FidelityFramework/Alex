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
    let readings =
        { graph.SourceReadings with Contexts = graph.SourceReadings.Contexts.Add(NodeId 4, [[inner]]) }
    let graph = { graph with SourceReadings = readings }
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

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``sibling movement cannot enter a source omitted position even when its body is live elsewhere`` omittedFirst =
    let first = node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let second = node 3 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let root = node 1 (SemanticKind.Sequential [first.Id; second.Id]) boolType [2; 3] None
    let graph = revision [root; first; second] |> declareTraversalReadings
    let omitted, admitted, omittedOrdinal, admittedOrdinal =
        if omittedFirst then first.Id, second.Id, 0, 1 else second.Id, first.Id, 1, 0
    // The body remains useful under another explicitly authored entry. The
    // contradictory local port/path rows must not override this position's
    // omission; observation must refuse instead of repairing the account.
    let paths = graph.SourceReadings.Contexts[omitted]
    let omission : ChildDisposition =
        { Ordinal = omittedOrdinal; Traversal = ChildTraversal.SourceOmitted(SupportKey.WholeOwningAnalysisRegion "fixture-owner", omitted) }
    let dispositions =
        graph.SourceReadings.Children[root.Id]
        |> List.map (fun current -> if current.Ordinal = omittedOrdinal then omission else current)
    let readings =
        { graph.SourceReadings with
            Contexts = graph.SourceReadings.Contexts.Add(omitted, [] :: paths)
            Entries = { Focus = omitted; Reason = SourceEntryReason.ExecutableRoot; Context = [] } :: graph.SourceReadings.Entries
            Children = graph.SourceReadings.Children.Add(root.Id, dispositions) }
    let graph = { graph with SourceReadings = readings }
    Assert.True((Zipper.createAt graph omitted []).IsSome)
    let rootPosition = Zipper.create graph root.Id |> require "Missing source root"
    let admittedPosition = Zipper.down admittedOrdinal rootPosition |> require "Missing admitted sibling"
    Assert.Equal(admitted, admittedPosition.Focus.Id)
    Assert.True((Zipper.down omittedOrdinal rootPosition).IsNone)
    let moved = if omittedFirst then Zipper.left admittedPosition else Zipper.right admittedPosition
    Assert.True(moved.IsNone)
    Assert.True((Zipper.createAt graph omitted paths.Head).IsNone)
    match RevisionNavigation.checkContext graph omitted paths.Head with
    | Error reason -> Assert.Contains("source omitted", reason)
    | Ok _ -> failwith "A declared path bypassed its source omitted child position"

[<Theory>]
[<InlineData("missing")>]
[<InlineData("incomplete")>]
[<InlineData("different-child")>]
[<InlineData("different-ordinal")>]
let ``an occurrence path cannot substitute for its complete matching child disposition`` defect =
    let graph = diamond ()
    let path = graph.SourceReadings.Contexts[NodeId 4].Head
    let parent = path.Head.Parent
    let account = graph.SourceReadings.Children[parent]
    let changed =
        match defect with
        | "missing" -> graph.SourceReadings.Children.Remove parent
        | "incomplete" -> graph.SourceReadings.Children.Add(parent, [])
        | "different-child" ->
            graph.SourceReadings.Children.Add(parent, [{ account.Head with Traversal = ChildTraversal.EnterLocal(NodeId 99) }])
        | _ -> graph.SourceReadings.Children.Add(parent, [{ account.Head with Ordinal = 99 }])
    let graph = { graph with SourceReadings = { graph.SourceReadings with Children = changed } }
    Assert.True((Zipper.createAt graph (NodeId 4) path).IsNone)
    match RevisionNavigation.checkContext graph (NodeId 4) path with
    | Error reason -> Assert.Contains("child disposition", reason)
    | Ok _ -> failwith "A missing or stale child disposition was accepted"

let private moduleDeclarationFixture () =
    let declaration = node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let container = node 1 (SemanticKind.ModuleDef("DeclaredModule", [declaration.Id])) unitType [] None
    revision [container; declaration] |> declareTraversalReadings

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``module declaration position reads its exact header with or without a container body`` bodyFree =
    let graph = moduleDeclarationFixture ()
    let path = graph.SourceReadings.Contexts[NodeId 2].Head
    Assert.Equal(OccurrencePort.ModuleDeclaration, path.Head.Port)
    let graph = if bodyFree then { graph with Nodes = graph.Nodes.Remove(NodeId 1) } else graph
    Assert.Equal<Result<NodeId, string>>(Ok(NodeId 1), RevisionNavigation.checkContext graph (NodeId 2) path)
    Assert.True((Zipper.createAt graph (NodeId 2) path).IsSome)

[<Theory>]
[<InlineData("missing")>]
[<InlineData("different-identity")>]
[<InlineData("different-port")>]
let ``a live module body cannot substitute for its exact typed declaration header`` defect =
    let graph = moduleDeclarationFixture ()
    let path = graph.SourceReadings.Contexts[NodeId 2].Head
    let parent = path.Head.Parent
    let header = graph.SourceReadings.ContextHeaders[parent]
    let headers =
        match defect with
        | "missing" -> graph.SourceReadings.ContextHeaders.Remove parent
        | "different-identity" -> graph.SourceReadings.ContextHeaders.Add(parent, { header with Identity = NodeId 99 })
        | _ ->
            let port = header.Ports[OccurrencePort.ModuleDeclaration]
            let changed = { header with Ports = header.Ports.Add(OccurrencePort.ModuleDeclaration, { port with Stamp = "another-port" }) }
            graph.SourceReadings.ContextHeaders.Add(parent, changed)
    let graph = { graph with SourceReadings = { graph.SourceReadings with ContextHeaders = headers } }
    Assert.True(graph.Nodes.ContainsKey parent)
    Assert.True((Zipper.createAt graph (NodeId 2) path).IsNone)
    match RevisionNavigation.checkContext graph (NodeId 2) path with
    | Error reason -> Assert.Contains("declaration context header", reason)
    | Ok _ -> failwith "A live container body concealed a missing or stale declaration header"

[<Fact>]
let ``declaring a component graph never silently enriches the empty revision helper`` () =
    let graph = revision [node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None]
    Assert.Empty graph.SourceReadings.Contexts
    Assert.Empty graph.SourceReadings.Children
    Assert.Empty graph.SourceReadings.BindingUses
    Assert.Empty graph.CurrentClaims
