module Alex.Tests.SourceEntryTraversalTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Traversal.CoverageValidation
open Alex.Tests.Build

// Traversal controls state synthetic source accounts. The observer refuses any
// occurrence outside the stated set; it never authors or repairs graph facts.
let private observe (allowed: Set<NodeId>) (graph: Revision) =
    let accumulator = MLIRAccumulator.empty ()
    let root = ref (ScopeContext.root ())
    let visited = ref Set.empty
    let probe : Nanopass =
        { Name = "source-entry-control"
          Witness = fun _ node ->
              Assert.Contains(node.Id, allowed)
              WitnessOutput.empty }
    runAllNanopasses [probe] graph (coeffects 64) accumulator root visited
    accumulator, root.Value, visited.Value

let private boundaryComponent () =
    let owner, declarationId, binding = NodeId 10, NodeId 11, NodeId 12
    let declaration : BoundaryImport =
        { Identity = declarationId; Binding = binding; Scope = owner
          Library = "component-test"; Symbol = "imported"; CallingConvention = "C"
          DeclarationPath = []; Parameters = []; Result = None
          Participants = Set.empty; SourceTypes = Map.empty; DeclarationFacts = Map.empty }
    let graph = Revision.empty "source-entry-component"
    let boundary =
        { graph.Emission.Boundary with
            Imports = Map.ofList [declarationId, declaration]
            ByScope = Map.ofList [owner, [declarationId]] }
    let graph =
        { graph with
            SourceReadings =
                { WitnessSourceReadings.empty with
                    Entries = [{ Focus = owner; Reason = SourceEntryReason.BoundaryScope; Context = [] }]
                    Contexts = Map.ofList [owner, [[]]]
                    ContextHeaders = Map.ofList [owner, { Identity = owner; Name = "Imports"; Ports = Map.empty }] }
            Emission = { graph.Emission with Boundary = boundary } }
    owner, declaration, graph

[<Fact>]
let ``source omitted position needs no inactive body during postorder traversal`` () =
    let local = node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let inactive = { node 3 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None with IsReachable = false }
    let parent = node 1 (SemanticKind.Sequential [local.Id; inactive.Id]) boolType [2; 3] None
    let declared = revision [parent; local; inactive] |> declareTraversalReadings
    let graph = { declared with Nodes = declared.Nodes.Remove inactive.Id }
    let expected = Set.ofList [parent.Id; local.Id]
    let accumulator, scope, visited = observe expected graph
    Assert.Empty accumulator.Errors
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty(ScopeContext.getOps scope)
    Assert.Equal<Set<NodeId>>(expected, visited)

[<Fact>]
let ``missing child account refuses before either child or parent witness`` () =
    let child = node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let parent = node 1 (SemanticKind.Sequential [child.Id]) boolType [2] None
    let declared = revision [parent; child] |> declareTraversalReadings
    let readings = { declared.SourceReadings with Children = declared.SourceReadings.Children.Remove parent.Id }
    let graph = { declared with SourceReadings = readings }
    let accumulator, scope, visited = observe Set.empty graph
    Assert.Contains(accumulator.Errors, fun diagnostic -> diagnostic.Message.Contains("no source-authored child disposition account"))
    Assert.DoesNotContain(child.Id, visited)
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty(ScopeContext.getOps scope)

[<Fact>]
let ``coverage detects unentered live body without consumer entry discovery`` () =
    let entered = node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let unentered = node 2 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let declared = revision [entered; unentered] |> declareTraversalReadings
    let readings =
        { declared.SourceReadings with
            Entries = declared.SourceReadings.Entries |> List.filter (fun entry -> entry.Focus = entered.Id) }
    let graph = { declared with SourceReadings = readings }
    let accumulator, _, visited = observe (Set.singleton entered.Id) graph
    Assert.Empty accumulator.Errors
    Assert.Equal<Set<NodeId>>(Set.singleton entered.Id, visited)
    let diagnostic = Assert.Single(validateCoverage graph visited)
    Assert.Equal(Some unentered.Id, diagnostic.NodeId)
    Assert.Contains("did not witness required PSG occurrence", diagnostic.Message)

[<Fact>]
let ``visited entry still refuses another undeclared occurrence context`` () =
    let body = node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let declared = revision [body] |> declareTraversalReadings
    let entry = Assert.Single declared.SourceReadings.Entries
    let stale : OccurrenceBreadcrumb =
        { Parent = NodeId 9000; Port = OccurrencePort.StructuralChild
          Ordinal = 0; Extent = 1; Stamp = "stale-parent-port" }
    let readings = { declared.SourceReadings with Entries = [entry; { entry with Context = [stale] }] }
    let graph = { declared with SourceReadings = readings }
    let accumulator, scope, visited = observe (Set.singleton body.Id) graph
    Assert.Equal<Set<NodeId>>(Set.singleton body.Id, visited)
    let diagnostic = Assert.Single accumulator.Errors
    Assert.Contains("whole occurrence path is not in the source context inventory", diagnostic.Message)
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty(ScopeContext.getOps scope)

[<Fact>]
let ``body-free boundary entry witnesses its assigned imports without declaration bodies`` () =
    let owner, declaration, graph = boundaryComponent ()
    // This is a component observation of the declared import account; full
    // source acceptance additionally requires its ABI/support declaration facts.
    let accumulator, scope, visited = observe Set.empty graph
    Assert.Empty graph.Nodes
    Assert.Empty accumulator.Errors
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty visited
    Assert.Equal<Set<NodeId>>(Set.singleton owner, accumulator.BoundaryScopes)
    Assert.Equal<MLIROp list>([FuncOp(BoundaryFuncDecl declaration)], ScopeContext.getOps scope)
    Assert.Empty(validateCoverage graph visited)
    Assert.Empty(validateBoundaryCoverage graph accumulator.BoundaryScopes)
    let missing = Assert.Single(validateBoundaryCoverage graph (accumulator.BoundaryScopes.Remove owner))
    Assert.Equal(Some owner, missing.NodeId)
    Assert.Contains("required source boundary scope 'Imports'", missing.Message)

[<Fact>]
let ``duplicate admitted body-free boundary entries emit and cover their imports once`` () =
    let owner, declaration, graph = boundaryComponent ()
    let entry = Assert.Single graph.SourceReadings.Entries
    let readings = { graph.SourceReadings with Entries = [entry; entry] }
    let graph = { graph with SourceReadings = readings }
    let accumulator, scope, visited = observe Set.empty graph
    Assert.Empty graph.Nodes
    Assert.Empty accumulator.Errors
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty visited
    Assert.Equal<Set<NodeId>>(Set.singleton owner, accumulator.BoundaryScopes)
    Assert.Equal<MLIROp list>([FuncOp(BoundaryFuncDecl declaration)], ScopeContext.getOps scope)
    Assert.Empty(validateCoverage graph visited)
    Assert.Empty(validateBoundaryCoverage graph accumulator.BoundaryScopes)

[<Theory>]
[<InlineData(0, "no assigned import plan")>]
[<InlineData(1, "names an absent declaration")>]
[<InlineData(2, "different source owner scope")>]
let ``failed body-free import plan never discharges coverage or installs the scope`` (fault: int) (expectedReason: string) =
    let owner, declaration, graph = boundaryComponent ()
    let boundary =
        match fault with
        | 0 -> { graph.Emission.Boundary with ByScope = Map.empty }
        | 1 -> { graph.Emission.Boundary with Imports = Map.empty }
        | 2 ->
            { graph.Emission.Boundary with
                Imports = Map.ofList [declaration.Identity, { declaration with Scope = NodeId 9000 }] }
        | _ -> failwith "Unknown import-plan control"
    let entry = Assert.Single graph.SourceReadings.Entries
    let readings = { graph.SourceReadings with Entries = [entry; entry] }
    let graph = { graph with SourceReadings = readings; Emission = { graph.Emission with Boundary = boundary } }
    let accumulator, scope, visited = observe Set.empty graph
    // Both failed entries remain observable; the first refusal did not install
    // the scope or make its second declared occurrence disappear.
    Assert.Equal(2, accumulator.Errors.Length)
    Assert.All(accumulator.Errors, fun diagnostic -> Assert.Contains(expectedReason, diagnostic.Message))
    Assert.Empty visited
    Assert.Empty accumulator.BoundaryScopes
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty(ScopeContext.getOps scope)
    let missing = Assert.Single(validateBoundaryCoverage graph accumulator.BoundaryScopes)
    Assert.Equal(Some owner, missing.NodeId)
    Assert.Contains("required source boundary scope 'Imports'", missing.Message)

[<Fact>]
let ``body-free boundary coverage diagnoses a missing context header without loading a body`` () =
    let owner, _, graph = boundaryComponent ()
    let readings = { graph.SourceReadings with ContextHeaders = Map.empty }
    let graph = { graph with SourceReadings = readings }
    let accumulator, scope, visited = observe Set.empty graph
    let refusal = Assert.Single accumulator.Errors
    Assert.Contains("focus has no live body or context header", refusal.Message)
    Assert.Empty visited
    Assert.Empty accumulator.BoundaryScopes
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty(ScopeContext.getOps scope)
    let missing = Assert.Single(validateBoundaryCoverage graph accumulator.BoundaryScopes)
    Assert.Equal(Some owner, missing.NodeId)
    Assert.Contains("matching body-free context account is absent", missing.Message)

[<Fact>]
let ``installed boundary owner still refuses an undeclared duplicate entry context`` () =
    let owner = NodeId 10
    let entry : SourceWitnessEntry =
        { Focus = owner; Reason = SourceEntryReason.BoundaryScope; Context = [] }
    let stale : OccurrenceBreadcrumb =
        { Parent = NodeId 9000; Port = OccurrencePort.ModuleDeclaration
          Ordinal = 0; Extent = 1; Stamp = "stale-declaration-port" }
    let graph = Revision.empty "duplicate-header-component"
    let readings =
        { WitnessSourceReadings.empty with
            Entries = [entry; { entry with Context = [stale] }]
            Contexts = Map.ofList [owner, [[]]]
            ContextHeaders = Map.ofList [owner, { Identity = owner; Name = "Imports"; Ports = Map.empty }] }
    let boundary = { graph.Emission.Boundary with ByScope = Map.ofList [owner, []] }
    let graph = { graph with SourceReadings = readings; Emission = { graph.Emission with Boundary = boundary } }
    let accumulator, scope, visited = observe Set.empty graph
    let diagnostic = Assert.Single accumulator.Errors
    Assert.Contains("whole occurrence path is not in the source context inventory", diagnostic.Message)
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty visited
    Assert.Equal<Set<NodeId>>(Set.singleton owner, accumulator.BoundaryScopes)
    Assert.Empty(ScopeContext.getOps scope)

[<Fact>]
let ``unclaimed reference diagnostic reads body-free binding contract`` () =
    let binding = NodeId 9000
    let reference = node 1 (SemanticKind.VarRef("Library.value", Some binding)) boolType [] None
    let declared = revision [reference] |> declareTraversalReadings
    let contract : BindingUseContract =
        { Binding = binding; Name = "value"; Class = SourceBindingClass.ImmutableValue
          IsProgramSlotIntent = false; HasProgramSlotAuthority = false
          IsFunctionBinding = false; IsCallableDeclaration = false; IsPartialApplication = false }
    let readings = { declared.SourceReadings with BindingUses = Map.ofList [reference.Id, contract] }
    let graph = { declared with SourceReadings = readings }
    let accumulator = MLIRAccumulator.empty ()
    let root = ref (ScopeContext.root ())
    let visited = ref Set.empty
    runAllNanopasses [] graph (coeffects 64) accumulator root visited
    let diagnostic = Assert.Single accumulator.Errors
    Assert.Contains("Binding 9000 (source declaration: value)", diagnostic.Message)
    Assert.DoesNotContain("not found in graph", diagnostic.Message)
    Assert.False(graph.Nodes.ContainsKey binding)
    Assert.Empty accumulator.NodeAssoc
    Assert.Empty accumulator.EmittedDefinitions
    Assert.Empty(ScopeContext.getOps root.Value)
