module Alex.Tests.SelectiveTraversalTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.SelectiveTraversal
open Alex.Tests.Build

// These fixtures exercise selection and current-occurrence authority separately
// from source checking. The small registry stands in for an ordinary function
// witness and deliberately refuses any retained body that is entered again.
let private fixture offset firstFingerprint secondFingerprint dependencies =
    let functionNodes number name =
        let body = node (offset + number) (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] (Some(offset + number + 1))
        let lambda = node (offset + number + 1)
                        (SemanticKind.Lambda([], body.Id, [], None, LambdaContext.RegularClosure))
                        (functionFrom unitType boolType) [offset + number] (Some(offset + number + 2))
        let binding = node (offset + number + 2) (SemanticKind.Binding(name, false, false, None)) lambda.Type [offset + number + 1] None
        let region fingerprint dependencies : WitnessRegion =
            { Identity = name; Flavor = WitnessRegionKind.ScalarCallable; Root = Some lambda.Id; Anchor = Some binding.Id
              Path = [{ Parent = binding.Id; Port = OccurrencePort.StructuralChild; Ordinal = 0; Extent = 1
                        Stamp = sprintf "fixture:structural:%d:%A" (NodeId.value binding.Id) binding.Children }]
              Members = Set.ofList [lambda.Id; body.Id]
              OwnerSupport = SupportKey.WholeOwningAnalysisRegion "fixture-owner"
              Supports = Set.singleton binding.Id; Fingerprint = fingerprint; Dependencies = dependencies }
        [body; lambda; binding], binding, region
    let firstNodes, first, firstRegion = functionNodes 0 "first"
    let secondNodes, second, secondRegion = functionNodes 3 "second"
    let common : WitnessRegion =
        { Identity = "common"; Flavor = WitnessRegionKind.Common; Root = None; Anchor = None; Path = []
          OwnerSupport = SupportKey.WholeOwningAnalysisRegion "fixture-owner"
          Members = Set.ofList [first.Id; second.Id]; Supports = Set.empty
          Fingerprint = "common-contract"; Dependencies = Set.empty }
    { revision (firstNodes @ secondNodes) with
        DeclarationRoots = [first.Id, DeclRoot.EntryPoint; second.Id, DeclRoot.EntryPoint]
        Codata =
            { Codata.empty with
                WitnessSegmentation = Some {
                    Version = 1; Regions = [common; firstRegion firstFingerprint Set.empty; secondRegion secondFingerprint dependencies] } } }
    |> declareTraversalReadings

let private registry (forbidden: Set<NodeId>) =
    let rec witness (context: WitnessContext) (node: SemanticNode) =
        if forbidden.Contains node.Id then failwithf "Retained node %A was re-witnessed" node.Id
        match node.Kind with
        | SemanticKind.Lambda(_, body, _, _, _) ->
            let zipper = atChild body context.Zipper
            visitAllNodes witness { context with Zipper = zipper } zipper.Focus context.TraversalVisited
            let name =
                match context.Graph.Nodes[context.Zipper.Path.Head.Parent].Kind with
                | SemanticKind.Binding(name, _, _, _) -> name
                | _ -> failwith "Fixture lost declaring binding"
            let operation = FuncOp(FuncDef(name, [], [], [FuncOp(Return [])], FuncVisibility.Private))
            { WitnessOutput.empty with TopLevelOps = [operation]; Result = TRVoid }
        | _ -> WitnessOutput.empty
    { Nanopasses = [{ Name = "selective-contract-fixture"; Witness = witness }] }

let private accepted (result: Result<Output, Alex.Traversal.MLIRTransfer.TransferRefusal>) =
    match result with
    | Ok value -> value
    | Result.Error failure -> failwith failure.Reason

let private refused expected (result: Result<Output, Alex.Traversal.MLIRTransfer.TransferRefusal>) =
    match result with
    | Ok _ -> failwith "Expected selective refusal"
    | Result.Error failure ->
        Assert.Contains(expected, failure.Reason)
        Assert.Empty failure.Witnessed

let private run graph previous forbidden =
    transferWithRegistry (registry forbidden) graph (coeffects 64) previous

let private segmentation (graph: Revision) = graph.Codata.WitnessSegmentation.Value
let private replaceRegions (graph: Revision) regions =
    { graph with Codata = { graph.Codata with WitnessSegmentation = Some { segmentation graph with Regions = regions } } }

// The source assigns an import entry separately from its exact body partition.
// This component states only the rows the declaration/traversal readers use.
let private boundaryScopeFixture () =
    let graph = fixture 0 "first" "second" Set.empty
    let scope, identity = NodeId 1000, NodeId 1001
    let declaration : BoundaryImport =
        { Identity = identity; Binding = NodeId 1002; Scope = scope
          Library = "selective-component"; Symbol = "imported"; CallingConvention = "C"
          DeclarationPath = []; Parameters = []; Result = None
          Participants = Set.empty; SourceTypes = Map.empty; DeclarationFacts = Map.empty }
    let readings =
        { graph.SourceReadings with
            Entries = graph.SourceReadings.Entries @ [{ Focus = scope; Reason = SourceEntryReason.BoundaryScope; Context = [] }]
            Contexts = graph.SourceReadings.Contexts.Add(scope, [[]])
            ContextHeaders = graph.SourceReadings.ContextHeaders.Add(scope, { Identity = scope; Name = "Imports"; Ports = Map.empty }) }
    let boundary =
        { graph.Emission.Boundary with
            Imports = Map.ofList [identity, declaration]; ByScope = Map.ofList [scope, [identity]] }
    { graph with SourceReadings = readings; Emission = { graph.Emission with Boundary = boundary } }, scope, declaration

[<Fact>]
let ``selective common witnesses body-free imports without escaping its exact body partition`` () =
    let graph, scope, declaration = boundaryScopeFixture ()
    let originalMembers = (segmentation graph).Regions |> List.map _.Members |> Set.unionMany
    Assert.Equal<Set<NodeId>>(graph.Nodes.Keys |> Set.ofSeq, originalMembers)
    Assert.DoesNotContain(scope, originalMembers)
    Assert.False(graph.Nodes.ContainsKey scope)
    let result = run graph None Set.empty |> accepted
    let common = result.Regions |> List.find (fun output -> output.Region.Flavor = WitnessRegionKind.Common)
    Assert.Equal<MLIROp list>([FuncOp(BoundaryFuncDecl declaration)], common.Operations)
    Assert.Equal<Set<NodeId>>(Set.ofList [NodeId 2; NodeId 5], common.Region.Members)
    Assert.Equal(2, result.Statistics.WitnessedNodes[common.Region.Identity])

[<Fact>]
let ``selective common refuses a missing body-free import plan without widening body membership`` () =
    let graph, scope, _ = boundaryScopeFixture ()
    let boundary = { graph.Emission.Boundary with ByScope = Map.empty }
    let graph = { graph with Emission = { graph.Emission with Boundary = boundary } }
    Assert.False(graph.Nodes.ContainsKey scope)
    Assert.DoesNotContain(scope, (segmentation graph).Regions |> List.map _.Members |> Set.unionMany)
    run graph None Set.empty |> refused "no assigned import plan"

[<Fact>]
let ``unchanged function bypasses witnesses and rebinds exact current occurrence after node renumbering`` () =
    let before = fixture 0 "first-v1" "second-v1" Set.empty
    let initial = run before None Set.empty |> accepted
    let after = fixture 100 "first-v2" "second-v1" Set.empty
    let current = run after (Some initial.State) (Set.ofList [NodeId 103; NodeId 104]) |> accepted
    Assert.Equal<string list>(["second"], current.Statistics.Retained)
    Assert.Equal<string list>(["first"; "common"], current.Statistics.Changed)
    Assert.Equal(0, current.Statistics.WitnessedNodes["second"])
    Assert.Equal(2, current.Statistics.WitnessedNodes["first"])
    let oldDefinition = initial.Regions |> List.find (fun region -> region.Region.Identity = "second") |> _.Definitions |> List.exactlyOne
    let definition = current.Regions |> List.find (fun region -> region.Region.Identity = "second") |> _.Definitions |> List.exactlyOne
    Assert.Same(oldDefinition.Operation, definition.Operation)
    Assert.Same(after.Nodes[NodeId 104], definition.Occurrence.Focus)
    Assert.Equal(NodeId 105, definition.Occurrence.Anchor)
    Assert.NotSame(oldDefinition.Occurrence.Focus, definition.Occurrence.Focus)
    Assert.Equal(Ok (), Alex.Correspondence.validateOccurrence current.Scope definition.Occurrence)
    match Alex.Correspondence.validateOccurrence current.Scope oldDefinition.Occurrence with
    | Result.Error reason -> Assert.Contains("different checked graph", reason)
    | Ok () -> failwith "Old occurrence was accepted"

[<Fact>]
let ``changed source dependency invalidates unchanged dependent fingerprint`` () =
    let first = fixture 0 "first-v1" "second-v1" (Set.singleton "first") |> fun graph -> run graph None Set.empty |> accepted
    let second = fixture 100 "first-v2" "second-v1" (Set.singleton "first") |> fun graph -> run graph (Some first.State) Set.empty |> accepted
    Assert.Empty second.Statistics.Retained
    Assert.Equal(2, second.Statistics.WitnessedNodes["second"])

[<Fact>]
let ``missing stale and overlapping published region coverage refuses before witnesses`` () =
    let graph = fixture 0 "first" "second" Set.empty
    let regions = (segmentation graph).Regions
    let missing = regions |> List.map (fun region -> if region.Identity = "common" then { region with Members = Set.empty } else region)
    run (replaceRegions graph missing) None Set.empty |> refused "does not exactly cover"
    let overlap = regions |> List.map (fun region -> if region.Identity = "common" then { region with Members = region.Members.Add(NodeId 0) } else region)
    run (replaceRegions graph overlap) None Set.empty |> refused "overlapping members"
    let path = regions |> List.map (fun region -> if region.Identity = "first" then { region with Path = [] } else region)
    run (replaceRegions graph path) None Set.empty |> refused "actual current PSG focus and Huet path"

[<Fact>]
let ``stale retained breadcrumb cannot enter accepted state`` () =
    let graph = fixture 0 "first" "second" Set.empty
    let previous = run graph None Set.empty |> accepted
    let next = fixture 100 "first" "second" Set.empty
    let malformed = (segmentation next).Regions |> List.map (fun region ->
        if region.Identity = "second" then
            { region with Anchor = Some(NodeId 2)
                          Path = [{ region.Path.Head with Parent = NodeId 2 }] }
        else region)
    run (replaceRegions next malformed) (Some previous.State) Set.empty
    |> refused "whole occurrence path is not in the source context inventory"

[<Fact>]
let ``retired region is absent from assembled operations and reported`` () =
    let graph = fixture 0 "first" "second" Set.empty
    let previous = run graph None Set.empty |> accepted
    let next =
        { graph with Nodes = graph.Nodes |> Map.filter (fun id _ -> NodeId.value id < 3)
                     DeclarationRoots = graph.DeclarationRoots |> List.take 1 }
        |> declareTraversalReadings
    let regions = (segmentation graph).Regions |> List.filter (fun region -> region.Identity <> "second") |> List.map (fun region ->
        if region.Identity = "common" then { region with Members = Set.singleton(NodeId 2); Fingerprint = "common-retired" } else region)
    let current = run (replaceRegions next regions) (Some previous.State) (Set.ofList [NodeId 0; NodeId 1]) |> accepted
    Assert.Equal<string list>(["second"], current.Statistics.Retired)
    Assert.Equal<string list>(["first"], current.Definitions |> List.choose (fun definition -> Alex.Correspondence.definitionSymbol definition.Operation))

[<Fact>]
let ``changed target coeffects prevent retained operation reuse`` () =
    let graph = fixture 0 "first" "second" Set.empty
    let previous = run graph None Set.empty |> accepted
    let current = transferWithRegistry (registry Set.empty) graph (coeffects 32) (Some previous.State) |> accepted
    Assert.Empty current.Statistics.Retained
