module Alex.Tests.BindingUseTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.ScopeContext
open Alex.Tests.Build

let private binding = NodeId 1
let private reading = node 2 (SemanticKind.VarRef("value", Some binding)) boolType [] None

/// The component has one live reading and an imported binding-use/physical
/// contract. No binding body is supplied or reconstructed by observation.
let private fixture bindingClass =
    let account : BindingUseContract =
        { Binding = binding; Name = "value"; Class = bindingClass
          IsProgramSlotIntent = false; HasProgramSlotAuthority = false
          IsFunctionBinding = false; IsCallableDeclaration = false; IsPartialApplication = false }
    let graph = revision [reading]
    { graph with
        SourceReadings = { graph.SourceReadings with BindingUses = Map.ofList [reading.Id, account] }
        Emission =
            { graph.Emission with
                Callable =
                    { graph.Emission.Callable with
                        ValueShapes = Map.ofList [reading.Id, CallableValueShape.Data reading.Id]
                        AliasTargets = Map.ofList [reading.Id, reading.Id; binding, binding] }
                Numeric =
                    { graph.Emission.Numeric with
                        OccurrenceRepresentations =
                            [reading.Id; binding] |> List.map (fun id -> id, Ok(ValueRepresentation.Scalar SettledSlot.Bool)) |> Map.ofList } } }
    |> declareTraversalReadings

let private observe (graph: Revision) =
    let position = focus graph graph.Nodes[reading.Id]
    let accumulator = MLIRAccumulator.empty ()
    let scope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    let ctx : WitnessContext =
        { Graph = graph; Zipper = position; Coeffects = coeffects 64
          Accumulator = accumulator; RootAccumulator = accumulator
          ScopeContext = scope; RootScopeContext = scope
          GlobalVisited = visited; TraversalVisited = visited }
    ctx, accumulator

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``formal and immutable reference use published binding accounts without binding bodies`` formal =
    let graph = fixture (if formal then SourceBindingClass.Formal else SourceBindingClass.ImmutableValue)
    Assert.False(graph.Nodes.ContainsKey binding)
    let ctx, accumulator = observe graph
    MLIRAccumulator.bindNode binding (Arg 7) (TInt(IntWidth 1)) accumulator
    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx reading
    match output.Result with
    | TRValue value ->
        Assert.Equal<SSA>(Arg 7, value.SSA)
        Assert.Equal<MLIRType>(TInt(IntWidth 1), value.Type)
    | other -> failwithf "Settled imported binding reading was refused: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps

[<Fact>]
let ``qualified use retains its declaration name without demanding the binding body`` () =
    let graph = fixture SourceBindingClass.ImmutableValue
    let qualified = { reading with Kind = SemanticKind.VarRef("Library.value", Some binding) }
    let graph = { graph with Nodes = graph.Nodes.Add(qualified.Id, qualified) }
    Assert.Equal("value", graph.SourceReadings.BindingUses[qualified.Id].Name)
    Assert.False(graph.Nodes.ContainsKey binding)
    let ctx, accumulator = observe graph
    MLIRAccumulator.bindNode binding (Arg 7) (TInt(IntWidth 1)) accumulator
    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx qualified
    match output.Result with
    | TRValue value -> Assert.Equal<SSA>(Arg 7, value.SSA)
    | other -> failwithf "Qualified source binding reading was refused: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps

[<Fact>]
let ``mutable reference uses its published cell class without a binding body`` () =
    let graph = fixture SourceBindingClass.MutableCell
    let ctx, accumulator = observe graph
    MLIRAccumulator.bindNode binding (Arg 7) (TMemRefStatic(1, TInt(IntWidth 1))) accumulator
    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx reading
    match output.Result with
    | TRValue value ->
        Assert.Equal<MLIRType>(TInt(IntWidth 1), value.Type)
        Assert.Equal<SSA>(V(2, 1), value.SSA)
    | other -> failwithf "Settled imported cell reading was refused: %A" other
    Assert.Equal(2, output.InlineOps.Length)

[<Theory>]
[<InlineData("missing")>]
[<InlineData("different-binding")>]
[<InlineData("unadmitted-program-slot")>]
[<InlineData("missing-slot-representation")>]
let ``missing or stale binding use refuses rather than inline forwarding a recalled value`` defect =
    let graph = fixture SourceBindingClass.ImmutableValue
    let account = graph.SourceReadings.BindingUses[reading.Id]
    let accounts =
        match defect with
        | "missing" -> Map.empty
        | "different-binding" -> Map.ofList [reading.Id, { account with Binding = NodeId 99 }]
        | "missing-slot-representation" -> Map.ofList [reading.Id, { account with IsProgramSlotIntent = true; HasProgramSlotAuthority = true }]
        | _ -> Map.ofList [reading.Id, { account with IsProgramSlotIntent = true; HasProgramSlotAuthority = false }]
    let graph = { graph with SourceReadings = { graph.SourceReadings with BindingUses = accounts } }
    let graph =
        if defect = "missing-slot-representation" then
            let numeric =
                { graph.Emission.Numeric with
                    OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations.Remove binding }
            { graph with Emission = { graph.Emission with Numeric = numeric } }
        else graph
    let ctx, accumulator = observe graph
    MLIRAccumulator.bindNode binding (Arg 7) (TInt(IntWidth 1)) accumulator
    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx reading
    match output.Result with
    | TRError diagnostic ->
        Assert.Equal(Some reading.Id, diagnostic.NodeId)
        let reason =
            match defect with
            | "missing" -> "omitted the source-owned binding use"
            | "different-binding" -> "names binding 99"
            | "missing-slot-representation" -> "lacks the physical representation of program slot 1"
            | _ -> "did not admit physical program slot authority"
        Assert.Contains(reason, diagnostic.Message)
    | other -> failwithf "Missing or stale source binding use was witnessed: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.True((MLIRAccumulator.recallNode reading.Id accumulator).IsNone)
