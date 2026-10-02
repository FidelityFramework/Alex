module Alex.Tests.TraversalOccurrenceTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

// The rows below are what the compiler service publishes for each fixture of this
// file. They were printed from the compiler service and copied here.

/// The target of the numeric domain relation. It is unreachable and no witness visits it.
let private numericDomain number =
    { node number (SemanticKind.Literal NativeLiteral.Unit) unitType [] None with IsReachable = false }

/// The Callable rows of nodes that hold data and alias no other node.
let private dataRows (held: SemanticNode list) : CallableEmissionProjection =
    let ids = held |> List.map (fun held -> held.Id)
    { Empty.callable with
        ValueShapes = ids |> List.map (fun id -> id, CallableValueShape.Data id) |> Map.ofList
        AliasTargets = ids |> List.map (fun id -> id, id) |> Map.ofList
        UnitNodes = held |> List.filter (fun held -> TypeIdentity.isUnit held.Type) |> List.map (fun held -> held.Id) |> Set.ofList
        ClosedData = Set.ofList ids
        Supports = ids |> List.map (fun id -> id, Set.singleton id) |> Map.ofList }

/// The carrier of a Boolean occurrence. The participants include the numeric domain node.
let private boolCarrier (site: SemanticNode) (participants: SemanticNode list) : ScalarCarrier =
    { Site = site.Id; Slot = SettledSlot.Bool; Range = ValueRange.Bounded(0I, 1I)
      Representation = None; Declaration = None; SourceType = boolType; Obligations = []
      Participants = participants |> List.map (fun held -> held.Id) |> Set.ofList }

let private boolForm : Result<ValueRepresentation, string> = Ok(ValueRepresentation.Scalar SettledSlot.Bool)

/// The Numeric rows of a fixture whose occurrences are all Boolean. Every carrier
/// published for these fixtures is a required one.
let private boolRows (carriers: ScalarCarrier list) (results: SemanticNode list) : NumericWitnessProjection =
    { Empty.numeric with
        Values = carriers |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList
        Required = carriers |> List.map (fun carrier -> carrier.Site) |> Set.ofList
        ResultSites = results |> List.map (fun held -> held.Id) |> Set.ofList
        SourceTypes = carriers |> List.map (fun carrier -> carrier.Site, boolType) |> Map.ofList
        OccurrenceRepresentations = carriers |> List.map (fun carrier -> carrier.Site, boolForm) |> Map.ofList
        TypeRepresentations = Map.ofList [boolType, boolForm] }

/// One Boolean literal, as published.
let private single (value: SemanticNode) : Revision =
    let domain = numericDomain 1
    { revision [value; domain] with
        Emission =
            { Empty.emission with
                Callable = dataRows [value]
                Numeric = boolRows [boolCarrier value [value; domain]] [value] } }

let private context graph position visited =
    let accumulator = MLIRAccumulator.empty ()
    let scope = ref (ScopeContext.root ())
    { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
      ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
      GlobalVisited = visited; TraversalVisited = visited }

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``driver rejects a foreign occurrence even if its node was previously visited`` alreadyVisited =
    let value = node 0 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let root = node 1 (SemanticKind.Sequential [value.Id]) boolType [0] None
    let domain = numericDomain 2
    let graph =
        { revision [value; root; domain] with
            Emission =
                { Empty.emission with
                    Callable = dataRows [value; root]
                    Numeric =
                        boolRows [boolCarrier value [value; domain]; boolCarrier root [value; root; domain]]
                                 [value; root] } }
    let position = Zipper.create graph root.Id |> require "Missing root"
    let initial = if alreadyVisited then Set.singleton value.Id else Set.empty
    let visited = ref initial
    let ctx = context graph position visited
    let mutable observed = false
    visitAllNodes (fun _ _ -> observed <- true; WitnessOutput.skip) ctx value visited
    Assert.False observed
    Assert.Equal<Set<NodeId>>(initial, visited.Value)
    Assert.Single ctx.Accumulator.Errors |> ignore
    Assert.Empty (ScopeContext.getOps ctx.ScopeContext.Value)

[<Fact>]
let ``driver rejects a zipper from another graph snapshot before witnessing`` () =
    let value = node 0 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let oldGraph = single value
    let graph = { oldGraph with DeclarationRoots = [value.Id, DeclRoot.EntryPoint] }
    let position = Zipper.create oldGraph value.Id |> require "Missing old occurrence"
    let visited = ref Set.empty
    let ctx = context graph position visited
    let mutable observed = false
    visitAllNodes (fun _ _ -> observed <- true; WitnessOutput.skip) ctx graph.Nodes[value.Id] visited
    Assert.False observed
    Assert.Empty visited.Value
    Assert.Single ctx.Accumulator.Errors |> ignore

[<Fact>]
let ``an explicitly invalidated source projection cannot enter transfer or claim coverage`` () =
    let value = node 0 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    // The revision as the compiler service publishes it: every node held has its
    // rows, the widths are declared and the literal is the root.
    let original =
        let published = single value
        let held = published.Nodes |> Map.toList |> List.map snd
        { published with
            DeclarationRoots = [value.Id, DeclRoot.EntryPoint]
            Platform = { published.Platform with Register = Ok 64; Pointer = Ok 64 }
            Emission = { published.Emission with Callable = dataRows held } }
    Assert.Empty(Integrity.check original)
    // The compiler service refuses to publish the invalidated graph. The revision
    // given to Alex holds the same nodes and states no emission row. Alex examines
    // a revision once, at its entry, and no witness runs for one it refuses.
    let graph = { original with Emission = Empty.emission }
    let request revision : Alex.Generation.Request =
        { Revision = revision; Target = Alex.Target.CPU; LinkedLibraries = Set.empty }
    match Alex.Generation.generate (request graph) with
    | Result.Error refusal ->
        Assert.Contains("The revision is not well formed.", refusal.Reason)
        Assert.Contains("Node 0 is named by Nodes and has no row in Emission.Callable.ValueShapes.", refusal.Reason)
        Assert.Contains("Node 0 is named by Nodes (reachable) and has no row in Emission.Numeric.SourceTypes.", refusal.Reason)
        Assert.Empty refusal.Witnessed
    | Result.Ok _ -> failwith "An unpublished graph entered production witnessing"
    // The revision with its rows is not refused for its form.
    match Alex.Generation.generate (request original) with
    | Result.Error refusal -> Assert.DoesNotContain("The revision is not well formed.", refusal.Reason)
    | Result.Ok witnessed -> Assert.NotEmpty witnessed.Operations
    Assert.Single(Alex.Traversal.CoverageValidation.validateCoverage graph Set.empty) |> ignore

[<Fact>]
let ``match scrutinee bindings guard and body retain the declared structural occurrence`` () =
    // The match selects by the case of a union. Baker settles a constant arm as a typed
    // equality and a conditional, so a match that reaches Alex has no constant arm.
    let inputType = optionOf boolType
    let scrutinee = node 0 (SemanticKind.PatternBinding "input") inputType [] None
    let initial = node 1 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let binding = node 2 (SemanticKind.Binding("condition", false, false, None)) boolType [1] None
    let read = node 3 (SemanticKind.VarRef("condition", Some binding.Id)) boolType [] None
    let guard = node 4 (SemanticKind.Sequential [read.Id]) boolType [3] None
    let yes = node 5 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let no = node 6 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let fallback = node 7 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let guarded = node 8 (SemanticKind.IfThenElse(guard.Id, yes.Id, Some no.Id)) boolType [4; 5; 6] None
    let selected = node 9 (SemanticKind.Sequential [binding.Id; guarded.Id]) boolType [2; 8] None
    let arms =
        [{ Pattern = Pattern.Union("Some", 1, Some Pattern.Wildcard, inputType); Bindings = []; Guard = None; Body = selected.Id }
         { Pattern = Pattern.Wildcard; Bindings = []; Guard = None; Body = fallback.Id }]
    let choice = node 10 (SemanticKind.CaseElimination(scrutinee.Id, arms)) boolType [0; 9; 7] None
    let root = node 11 (SemanticKind.Sequential [choice.Id]) boolType [10] None
    let domain = numericDomain 12
    let program = [scrutinee; initial; binding; read; guard; yes; no; fallback; guarded; selected; choice; root]
    let callable = dataRows program
    let unsettled : Result<ValueRepresentation, string> = Result.Error "Union has no complete source-settled representation."
    let numeric =
        boolRows
            [ boolCarrier initial [initial; domain]
              boolCarrier binding [binding; domain]
              boolCarrier read [binding; read; domain]
              boolCarrier guard [read; guard; domain]
              boolCarrier yes [yes; domain]
              boolCarrier no [no; domain]
              boolCarrier fallback [fallback; domain]
              boolCarrier guarded [guard; yes; no; guarded; domain]
              boolCarrier selected [binding; guarded; selected; domain]
              boolCarrier choice [scrutinee; fallback; selected; choice; domain]
              boolCarrier root [choice; root; domain] ]
            [initial; read; guard; yes; no; fallback; guarded; selected; choice; root]
    let graph =
        { revision (program @ [domain]) with
            Emission =
                { Empty.emission with
                    Callable =
                        { callable with
                            Symbols = Map.ofList [binding.Id, CallableSymbolName.RootBinding "condition"]
                            AliasTargets = callable.AliasTargets |> Map.add binding.Id initial.Id |> Map.add read.Id initial.Id
                            Supports =
                                callable.Supports
                                |> Map.add binding.Id (Set.ofList [initial.Id; binding.Id])
                                |> Map.add read.Id (Set.ofList [initial.Id; binding.Id; read.Id]) }
                    Numeric =
                        { numeric with
                            SourceTypes = numeric.SourceTypes.Add(scrutinee.Id, inputType)
                            OccurrenceRepresentations = numeric.OccurrenceRepresentations.Add(scrutinee.Id, unsettled)
                            TypeRepresentations = numeric.TypeRepresentations.Add(inputType, unsettled) } } }
    let graph = declareBindingReadings graph
    let position = Zipper.create graph root.Id |> require "Missing root"
    let visited = ref Set.empty
    let ctx = context graph position visited
    // The scrutinee is a formal. Its operand is the byte view of the union it holds.
    let scrutineeType = TMemRef(TInt(IntWidth 8))
    MLIRAccumulator.bindNode scrutinee.Id (Arg 0) scrutineeType ctx.Accumulator
    let occurrences = ResizeArray<NodeId * NodeId list>()
    let expected =
        Map.ofList [scrutinee.Id, [choice.Id; root.Id]
                    binding.Id, [selected.Id; choice.Id; root.Id]
                    guard.Id, [guarded.Id; selected.Id; choice.Id; root.Id]
                    read.Id, [guard.Id; guarded.Id; selected.Id; choice.Id; root.Id]
                    yes.Id, [guarded.Id; selected.Id; choice.Id; root.Id]
                    no.Id, [guarded.Id; selected.Id; choice.Id; root.Id]
                    fallback.Id, [choice.Id; root.Id]]
    let rec witness ctx (node: SemanticNode) =
        Assert.Equal(node.Id, ctx.Zipper.Focus.Id)
        if Map.containsKey node.Id expected then
            occurrences.Add(node.Id, ctx.Zipper.Path |> List.map (fun step -> step.Parent))
        match node.Kind with
        | SemanticKind.CaseElimination _ -> (Alex.Witnesses.MatchWitness.createNanopass (fun () -> witness)).Witness ctx node
        | SemanticKind.IfThenElse _ -> (Alex.Witnesses.ControlFlowWitness.createNanopass (fun () -> witness)).Witness ctx node
        | SemanticKind.Binding _ -> Alex.Witnesses.BindingWitness.nanopass.Witness ctx node
        | SemanticKind.VarRef _ -> Alex.Witnesses.VarRefWitness.nanopass.Witness ctx node
        | SemanticKind.Literal _ -> Alex.Witnesses.LiteralWitness.nanopass.Witness ctx node
        | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    visitAllNodes witness ctx position.Focus visited
    Assert.Empty ctx.Accumulator.Errors
    Assert.Equal(expected.Count, occurrences.Count)
    for id, path in occurrences do
        Assert.Equal<NodeId list>(expected[id], path)
    let result, resultType = MLIRAccumulator.recallNode root.Id ctx.Accumulator |> require "Match lost its result"
    let body = ScopeContext.getOps ctx.ScopeContext.Value @ [MLIROp.FuncOp(FuncOp.Return [{ SSA = result; Type = resultType }])]
    let declaration = MLIROp.FuncOp(FuncOp.FuncDef("match_occurrences", [Arg 0, scrutineeType], [resultType], body, FuncVisibility.Private))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "match_occurrences" [declaration]
    Alex.Tests.Tools.mlirOpt ["--verify-each"] text |> ignore

[<Fact>]
let ``match refuses an unsettled source guard before visiting any child`` () =
    let value = node 0 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let arm = { Pattern = Pattern.Wildcard; Bindings = []; Guard = Some value.Id; Body = value.Id }
    let choice = node 1 (SemanticKind.CaseElimination(value.Id, [arm])) boolType [0; 0; 0] None
    let domain = numericDomain 2
    let graph =
        { revision [value; choice; domain] with
            Emission =
                { Empty.emission with
                    Callable = dataRows [value; choice]
                    Numeric =
                        boolRows [boolCarrier value [value; domain]; boolCarrier choice [value; choice; domain]]
                                 [value; choice] } }
    let position = Zipper.create graph choice.Id |> require "Missing match"
    let visited = ref Set.empty
    let ctx = context graph position visited
    let mutable observed = false
    let output =
        (Alex.Witnesses.MatchWitness.createNanopass (fun () -> fun _ _ -> observed <- true; WitnessOutput.skip)).Witness ctx position.Focus
    Assert.False observed
    match output.Result with TRError _ -> () | other -> failwithf "Expected selected-scope diagnostic, got %A" other
    Assert.Empty output.InlineOps
