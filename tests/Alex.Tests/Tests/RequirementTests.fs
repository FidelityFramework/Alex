module Alex.Tests.RequirementTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
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

/// The Numeric rows. Every carrier published for these fixtures is a required one.
let private numericRows (carriers: ScalarCarrier list) (results: SemanticNode list)
                        (occurrences: (SemanticNode * Result<ValueRepresentation, string>) list)
                        (types: (TypeIdentity * Result<ValueRepresentation, string>) list) : NumericWitnessProjection =
    { Empty.numeric with
        Values = carriers |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList
        Required = carriers |> List.map (fun carrier -> carrier.Site) |> Set.ofList
        ResultSites = results |> List.map (fun held -> held.Id) |> Set.ofList
        SourceTypes = occurrences |> List.map (fun (held, _) -> held.Id, held.Type) |> Map.ofList
        OccurrenceRepresentations = occurrences |> List.map (fun (held, form) -> held.Id, form) |> Map.ofList
        TypeRepresentations = Map.ofList types }

let private boolForm : Result<ValueRepresentation, string> = Ok(ValueRepresentation.Scalar SettledSlot.Bool)
let private unitForm : Result<ValueRepresentation, string> = Ok(ValueRepresentation.Scalar SettledSlot.Unit)

let private fixture () =
    let condition = node 0 (SemanticKind.PatternBinding "condition") boolType [] None
    let body = node 1 (SemanticKind.Literal NativeLiteral.Unit) unitType [] None
    let required = node 2 (SemanticKind.Require(condition.Id, "Pattern match failed")) unitType [0] None
    let frontier = node 3 (SemanticKind.Sequential [required.Id; body.Id]) unitType [2; 1] None
    let root = node 4 (SemanticKind.Sequential [frontier.Id]) unitType [3] None
    let domain = numericDomain 5
    let program = [condition; body; required; frontier; root]
    let row =
        { Sources = [required.Id; condition.Id; body.Id]; Target = frontier.Id
          Class = EdgeClass.Provenance; Role = EdgeRole.MatchRequirement; Ordinal = 1 }
    let contract : RequirementWitness =
        { Site = required.Id; Condition = condition.Id; Diagnostic = "Pattern match failed"
          Frontier = frontier.Id; Continuation = body.Id; PatternTest = None
          Participants = [frontier.Id; required.Id; condition.Id; body.Id] }
    let emission =
        { Empty.emission with
            Callable = dataRows program
            Storage = { Empty.storage with Requirements = Map.ofList [required.Id, contract] }
            Numeric =
                numericRows [boolCarrier condition [condition; domain]] []
                    [condition, boolForm; body, unitForm; required, unitForm; frontier, unitForm; root, unitForm]
                    [boolType, boolForm; unitType, unitForm] }
    let graph =
        { revision (program @ [domain]) with
            Edges = [row]
            Emission = emission }
        |> declareTraversalReadings
    graph, root.Id, frontier.Id, required.Id, condition.Id

let private context graph root frontier site condition conditionType =
    let position = Zipper.create graph root |> require "Missing root" |> atChild frontier |> atChild site
    let accumulator = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode condition (Arg 0) conditionType accumulator
    let scope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
      ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
      GlobalVisited = visited; TraversalVisited = visited }

[<Theory>]
[<InlineData("missing-evidence")>]
[<InlineData("wrong-order")>]
[<InlineData("wrong-condition")>]
[<InlineData("foreign-position")>]
[<InlineData("foreign-snapshot")>]
[<InlineData("non-boolean")>]
let ``requirement rejects stale evidence operands and occurrences before emitting`` defect =
    let graph, root, frontier, site, condition = fixture ()
    let changed =
        match defect with
        | "missing-evidence" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.MatchRequirement) }
        | "wrong-order" ->
            let node = graph.Nodes[frontier]
            { graph with Nodes = graph.Nodes.Add(frontier, { node with Children = List.rev node.Children }) }
            |> declareTraversalReadings
        | "foreign-position" ->
            // A second actual occurrence is not the retained requirement's
            // frontier. Never manufacture an undeclared detached root.
            let alternate = node 6 (SemanticKind.Sequential [site]) unitType [NodeId.value site] None
            { graph with Nodes = graph.Nodes.Add(alternate.Id, alternate) }
            |> declareTraversalReadings
        | "wrong-condition" ->
            let edges =
                graph.Edges |> List.map (fun edge ->
                    if edge.Role = EdgeRole.MatchRequirement then { edge with Sources = [site; site; List.last edge.Sources] } else edge)
            { graph with Edges = edges }
        | _ -> graph
    // The compiler service refuses to publish the first three defects. The revision
    // given to Alex for them holds the changed graph and states no emission row.
    let changed =
        if List.contains defect ["missing-evidence"; "wrong-order"; "wrong-condition"] then
            { changed with Emission = Empty.emission }
        else changed
    let carrier = if defect = "non-boolean" then TInt(IntWidth 32) else TInt(IntWidth 1)
    let ctx = context changed root frontier site condition carrier
    let ctx =
        match defect with
        | "foreign-position" -> { ctx with Zipper = at changed 6 [NodeId.value site] }
        | "foreign-snapshot" -> { ctx with Graph = { changed with DeclarationRoots = [] } }
        | _ -> ctx
    let output = Alex.Witnesses.RequirementWitness.nanopass.Witness ctx ctx.Zipper.Focus
    match output.Result with TRError _ -> () | other -> failwithf "Expected requirement rejection: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``a selected singleton returns its existing body carrier without an invented join`` unionPattern =
    // The component fixture supplies already selected operands. Source admission
    // is tested by RequirementCases and the terminal native match controls.
    let inputType = if unionPattern then optionOf boolType else boolType
    let input = node 0 (SemanticKind.PatternBinding "input") inputType [] None
    let body = node 1 (SemanticKind.PatternBinding "selected") boolType [] None
    let selectedPattern =
        if unionPattern then Pattern.Union("Some", 1, Some Pattern.Wildcard, inputType)
        else Pattern.Const(NativeLiteral.Bool true)
    let arm = { Pattern = selectedPattern; Guard = None; Body = body.Id; Bindings = [] }
    let selected = node 2 (SemanticKind.CaseElimination(input.Id, [arm])) boolType [0; 1] None
    let domain = numericDomain 3
    let program = [input; body; selected]
    let unsettled : Result<ValueRepresentation, string> = Result.Error "Union has no complete source-settled representation."
    let inputCarriers = if unionPattern then [] else [boolCarrier input [input; domain]]
    let inputForm = if unionPattern then unsettled else boolForm
    let inputTypes = if unionPattern then [inputType, unsettled] else []
    let graph =
        { revision (program @ [domain]) with
            Emission =
                { Empty.emission with
                    Callable = dataRows program
                    Numeric =
                        numericRows
                            (inputCarriers @ [boolCarrier body [body; domain]; boolCarrier selected [input; body; selected; domain]])
                            [selected]
                            [input, inputForm; body, boolForm; selected, boolForm]
                            ([boolType, boolForm] @ inputTypes) } }
        |> declareTraversalReadings
    let position = Zipper.create graph selected.Id |> require "Missing selected match"
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode body.Id (Arg 1) (TInt(IntWidth 1)) operands
    let inputCarrier = if unionPattern then TMemRef(TInt(IntWidth 8)) else TInt(IntWidth 1)
    let inventedJoin = Alex.Traversal.Values.value selected.Id 0
    let parser =
        Alex.Patterns.ControlFlowPatterns.pBuildMatchElimination (Arg 0) inputCarrier input.Id
            [([], body.Id, arm)] (Some(inventedJoin, TInt(IntWidth 1))) selected.Id
    match unionPattern, matchAt parser position 64 operands with
    | false, Result.Error reason ->
        // Baker settles a constant arm as a typed equality and a conditional. An arm
        // that reaches Alex as a raw constant was not settled, and Alex refuses it.
        Assert.Contains("Raw constant CaseElimination requires Baker's typed equality and conditional normalization.", reason)
        Assert.Empty operands.AllOps
        Assert.True((MLIRAccumulator.recallNode selected.Id operands).IsNone)
    | true, Result.Ok ((operations, TRValue value), _) ->
        Assert.Empty operations
        Assert.Equal(Arg 1, value.SSA)
        Assert.NotEqual(inventedJoin, value.SSA)
        let definition = MLIROp.FuncOp(FuncOp.FuncDef("selected_body", [Arg 0, inputCarrier; Arg 1, value.Type],
            [value.Type], [MLIROp.FuncOp(FuncOp.Return [value])], FuncVisibility.Private))
        let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "selected_match" [definition]
        let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
        Assert.Contains("return %arg1 : i1", verified)
    | _, other -> failwithf "Selected body lost its carrier: %A" other

[<Fact>]
let ``portable requirement diagnostics preserve escaped UTF8 and embedded control bytes`` () =
    let message = "quoted \"message\" \\ newline\nUnicode λ 雪 NUL\000end"
    let declaration = MLIROp.FuncOp(FuncOp.FuncDef("diagnostic_bytes", [Arg 0, TInt(IntWidth 1)], [],
        [MLIROp.Assert(Arg 0, message); MLIROp.FuncOp(FuncOp.Return [])], FuncVisibility.Private))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "diagnostic_bytes" [declaration]
    Assert.Contains("\\22message\\22", text)
    Assert.Contains("\\CE\\BB", text)
    Assert.Contains("\\00end", text)
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    let roundTrip = Alex.Tests.Tools.mlirOpt ["--verify-each"] verified
    Assert.Equal(verified, roundTrip)
