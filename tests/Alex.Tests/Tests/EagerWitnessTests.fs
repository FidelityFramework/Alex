module Alex.Tests.EagerWitnessTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

let private context graph position accumulator =
    let scope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
      ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
      GlobalVisited = visited; TraversalVisited = visited }

// The rows below are what the compiler service publishes for each fixture of this file.
// They were printed from the compiler service and copied here. Every fixture holds
// values of the bool type and of the unit type only, and no callable.

let private identities numbers = numbers |> List.map NodeId

/// One of the four domain nodes that settlement adds to every fixture. No code under
/// test reads them. They are held because the carriers name the first of them, and
/// because the node numbers of the revision are then the published ones.
let private domain number =
    { node number (SemanticKind.Literal NativeLiteral.Unit) unitType [] None with IsReachable = false }

let private edge sources target edgeClass role ordinal : Hyperedge =
    { Sources = identities sources; Target = NodeId target; Class = edgeClass; Role = role; Ordinal = ordinal }

let private structural source target role = edge [source] target EdgeClass.Structural role 0

/// The demand relation of a marker, as an edge and as a row of the demand projection.
let private demandEdge marker operand =
    edge [marker; operand] marker EdgeClass.Demand (EdgeRole.EagerDemand EagerFrontier.Expression) 0

let private demandRelation marker operand : EagerDemandRelation =
    { Sources = identities [marker; operand]; Ordinal = 0; Frontier = Some EagerFrontier.Expression; IsDemand = true }

/// The carrier published for a value of the bool type.
let private boolean site participants : ScalarCarrier =
    { Site = NodeId site; Slot = SettledSlot.Bool; Range = ValueRange.Bounded(0I, 1I)
      Representation = None; Declaration = None; SourceType = boolType
      Obligations = []; Participants = Set.ofList (identities participants) }

let private carrierEdge (carrier: ScalarCarrier) : Hyperedge =
    { Sources = Set.toList carrier.Participants; Target = carrier.Site
      Class = EdgeClass.Range; Role = EdgeRole.NumericCarrier carrier; Ordinal = 0 }

/// The representation published for the two types these fixtures use.
let private formOf identity =
    if identity = boolType then ValueRepresentation.Scalar SettledSlot.Bool
    elif identity = unitType then ValueRepresentation.Scalar SettledSlot.Unit
    else failwithf "The fixtures of this file state no representation for %A" identity

/// The edges published among the nodes held: the relations the node kinds imply, the
/// demand relations and the carrier relations, in that order. The four domain edges
/// and the provenance edges of the domain nodes are left out. No code under test
/// reads an edge.
let private withEdges implied demands carriers (revision: Revision) =
    { revision with Edges = implied @ demands @ List.map carrierEdge carriers }

/// Every held node is published as data that names itself.
let private withData units (revision: Revision) =
    let held = revision.Nodes |> Map.toList |> List.map fst
    { revision with
        Emission =
            { revision.Emission with
                Callable =
                    { revision.Emission.Callable with
                        ValueShapes = held |> List.map (fun id -> id, CallableValueShape.Data id) |> Map.ofList
                        AliasTargets = held |> List.map (fun id -> id, id) |> Map.ofList
                        UnitNodes = Set.ofList (identities units)
                        ClosedData = Set.ofList held
                        Supports = held |> List.map (fun id -> id, Set.singleton id) |> Map.ofList } } }

/// The numeric projection: a carrier for every value of the bool type, the sites whose
/// result the traversal checks, and the type and representation of every reachable node.
let private withNumeric (carriers: ScalarCarrier list) results (revision: Revision) =
    let sources = revision.Nodes |> Map.filter (fun _ held -> held.IsReachable)
    { revision with
        Emission =
            { revision.Emission with
                Numeric =
                    { revision.Emission.Numeric with
                        Values = carriers |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList
                        Required = carriers |> List.map (fun carrier -> carrier.Site) |> Set.ofList
                        ResultSites = Set.ofList (identities results)
                        SourceTypes = sources |> Map.map (fun _ held -> held.Type)
                        OccurrenceRepresentations = sources |> Map.map (fun _ held -> Ok (formOf held.Type))
                        TypeRepresentations =
                            sources |> Map.toList |> List.map (fun (_, held) -> held.Type, Ok (formOf held.Type)) |> Map.ofList } } }

let private withDemand operands relations (revision: Revision) =
    { revision with Demand = { Operands = Map.ofList operands; Relations = Map.ofList relations } }

let private fixture () =
    let operand = node 0 (SemanticKind.PatternBinding "alreadyComputed") boolType [] None
    let marker = node 1 (SemanticKind.EagerExpr operand.Id) boolType [0] None
    let root = node 2 (SemanticKind.Sequential [marker.Id]) boolType [1] None
    let carriers = [boolean 0 [0; 3]; boolean 1 [0; 1; 3]; boolean 2 [1; 2; 3]]
    let graph =
        revision ([operand; marker; root] @ List.map domain [3; 4; 5; 6])
        |> withEdges [structural 0 1 EdgeRole.Subject; structural 1 2 EdgeRole.Element] [demandEdge 1 0] carriers
        |> withData [3; 4; 5; 6]
        |> withNumeric carriers [1; 2]
        |> withDemand [marker.Id, operand.Id] [marker.Id, [demandRelation 1 0]]
        |> declareTraversalReadings
    graph, root.Id, marker.Id, operand.Id

[<Fact>]
let ``explicit demand forwards its already witnessed operand without replaying effects`` () =
    let graph, root, marker, operand = fixture ()
    let accumulator = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode operand (Arg 0) (TInt(IntWidth 1)) accumulator
    let position = Zipper.create graph root |> require "Missing root" |> atChild marker
    let ctx = context graph position accumulator
    let output = Alex.Witnesses.EagerWitness.nanopass.Witness ctx position.Focus
    Assert.Equal(TRValue { SSA = Arg 0; Type = TInt(IntWidth 1) }, output.Result)
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Empty accumulator.AllOps
    Assert.Empty ctx.TraversalVisited.Value
    Assert.Same(position, ctx.Zipper)

[<Theory>]
[<InlineData("missing")>]
[<InlineData("duplicate")>]
[<InlineData("changed operand")>]
[<InlineData("wrong class")>]
[<InlineData("wrong ordinal")>]
[<InlineData("wrong frontier")>]
[<InlineData("malformed marker")>]
[<InlineData("missing value")>]
[<InlineData("foreign graph")>]
let ``explicit demand refuses stale authority or absent scoped values`` defect =
    let graph, root, marker, operand = fixture ()
    let row = graph.Edges |> List.find (fun edge -> edge.Target = marker && edge.Role = EdgeRole.EagerDemand EagerFrontier.Expression)
    let relation = graph.Demand.Relations[marker] |> List.exactlyOne
    // The revision states a demand relation twice: as an edge and as a row of the
    // demand projection. Each defect is stated in both. The relations the node kinds
    // imply and the carrier relations stay, as the compiler service publishes them
    // for the edited source.
    let replace updated projected =
        { graph with
            Edges = graph.Edges |> List.collect (fun edge -> if edge = row then updated else [edge])
            Demand = { graph.Demand with Relations = if List.isEmpty projected then Map.empty else Map.ofList [marker, projected] } }
    let graph =
        match defect with
        | "missing" -> replace [] []
        | "duplicate" -> replace [row; row] [relation; relation]
        | "changed operand" -> replace [{ row with Sources = [marker; root] }] [{ relation with Sources = [marker; root] }]
        | "wrong class" -> replace [{ row with Class = EdgeClass.Provenance }] [{ relation with IsDemand = false }]
        | "wrong ordinal" -> replace [{ row with Ordinal = 1 }] [{ relation with Ordinal = 1 }]
        | "wrong frontier" ->
            replace [{ row with Role = EdgeRole.EagerDemand EagerFrontier.Binding }] [{ relation with Frontier = Some EagerFrontier.Binding }]
        | "malformed marker" ->
            // A marker that holds no child has no operand row in the demand projection.
            { graph with
                Nodes = graph.Nodes.Add(marker, { graph.Nodes[marker] with Children = [] })
                Demand = { graph.Demand with Operands = Map.empty } }
        | _ -> graph
    let graph = declareTraversalReadings graph
    let accumulator = MLIRAccumulator.empty ()
    if defect <> "missing value" then MLIRAccumulator.bindNode operand (Arg 0) (TInt(IntWidth 1)) accumulator
    let position = Zipper.create graph root |> require "Missing root" |> atChild marker
    let ctx = context graph position accumulator
    let ctx = if defect = "foreign graph" then { ctx with Graph = { graph with DeclarationRoots = [] } } else ctx
    let output = Alex.Witnesses.EagerWitness.nanopass.Witness ctx position.Focus
    match output.Result with TRError _ -> () | other -> failwithf "Malformed demand was witnessed: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``an eager effect remains inside its conditional arm for either guard value`` active =
    let guard = node 0 (SemanticKind.Literal(NativeLiteral.Bool active)) boolType [] None
    let effect = node 1 (SemanticKind.PatternBinding "effectfulOperand") boolType [] None
    let marker = node 2 (SemanticKind.EagerExpr effect.Id) boolType [1] None
    let fallback = node 3 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let choice = node 4 (SemanticKind.IfThenElse(guard.Id, marker.Id, Some fallback.Id)) boolType [0; 2; 3] None
    let carriers = [boolean 0 [0; 5]; boolean 1 [1; 5]; boolean 2 [1; 2; 5]; boolean 3 [3; 5]; boolean 4 [0; 2; 3; 4; 5]]
    let graph =
        revision ([guard; effect; marker; fallback; choice] @ List.map domain [5; 6; 7; 8])
        |> withEdges
            [ structural 1 2 EdgeRole.Subject; structural 0 4 EdgeRole.Guard
              structural 2 4 EdgeRole.ThenBranch; structural 3 4 EdgeRole.ElseBranch ]
            [demandEdge 2 1] carriers
        |> withData [5; 6; 7; 8]
        |> withNumeric carriers [0; 2; 3; 4]
        |> withDemand [marker.Id, effect.Id] [marker.Id, [demandRelation 2 1]]
        |> declareTraversalReadings
    let accumulator = MLIRAccumulator.empty ()
    let position = Zipper.create graph choice.Id |> require "Missing conditional"
    let ctx = context graph position accumulator
    let effectValue = { SSA = Alex.Traversal.Values.value effect.Id 0; Type = TInt(IntWidth 1) }
    let visits = ResizeArray<NodeId>()
    let rec witness ctx (node: SemanticNode) =
        Assert.Equal(node.Id, ctx.Zipper.Focus.Id)
        if node.Id = effect.Id then
            visits.Add node.Id
            let parent = Zipper.up ctx.Zipper |> require "Effect lost its marker"
            let conditional = Zipper.up parent |> require "Marker lost its conditional"
            Assert.Equal(marker.Id, parent.Focus.Id)
            Assert.Equal(choice.Id, conditional.Focus.Id)
            { InlineOps = [MLIROp.FuncOp(FuncOp.FuncCall([effectValue], "observe_effect", []))]
              TopLevelOps = []; Result = TRValue effectValue }
        else
            match node.Kind with
            | SemanticKind.IfThenElse _ -> (Alex.Witnesses.ControlFlowWitness.createNanopass (fun () -> witness)).Witness ctx node
            | SemanticKind.EagerExpr _ -> Alex.Witnesses.EagerWitness.nanopass.Witness ctx node
            | SemanticKind.Literal _ -> Alex.Witnesses.LiteralWitness.nanopass.Witness ctx node
            | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    visitAllNodes witness ctx position.Focus ctx.TraversalVisited
    Assert.Empty accumulator.Errors
    Assert.Equal(effect.Id, Assert.Single visits)
    let operations = ScopeContext.getOps ctx.ScopeContext.Value
    Assert.DoesNotContain(operations, function MLIROp.FuncOp(FuncOp.FuncCall(_, "observe_effect", _)) -> true | _ -> false)
    let yes, no = operations |> List.choose (function MLIROp.SCFOp(SCFOp.If(_, yes, Some no, _)) -> Some(yes, no) | _ -> None) |> Assert.Single
    Assert.Single(yes |> List.filter (function MLIROp.FuncOp(FuncOp.FuncCall(_, "observe_effect", _)) -> true | _ -> false)) |> ignore
    Assert.DoesNotContain(no, function MLIROp.FuncOp(FuncOp.FuncCall(_, "observe_effect", _)) -> true | _ -> false)
    let result, resultType = MLIRAccumulator.recallNode choice.Id accumulator |> require "Conditional lost its value"
    let declaration = MLIROp.FuncOp(FuncOp.FuncDef("conditional_demand", [], [resultType],
        operations @ [MLIROp.FuncOp(FuncOp.Return [{ SSA = result; Type = resultType }])], FuncVisibility.Private))
    let effectDeclaration = MLIROp.FuncOp(FuncOp.FuncDecl("observe_effect", [], [TInt(IntWidth 1)], FuncVisibility.Private, []))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "conditional_demand" [effectDeclaration; declaration]
    Alex.Tests.Tools.mlirOpt ["--verify-each"] text |> ignore

let private unitFixture () =
    let effect = node 0 (SemanticKind.PatternBinding "consoleWritelnResult") unitType [] None
    let marker = node 1 (SemanticKind.EagerExpr effect.Id) unitType [0] None
    let root = node 2 (SemanticKind.Sequential [marker.Id]) unitType [1] None
    let graph =
        revision ([effect; marker; root] @ List.map domain [3; 4; 5; 6])
        |> withEdges [structural 0 1 EdgeRole.Subject; structural 1 2 EdgeRole.Element] [demandEdge 1 0] []
        |> withData [0; 1; 2; 3; 4; 5; 6]
        |> withNumeric [] []
        |> withDemand [marker.Id, effect.Id] [marker.Id, [demandRelation 1 0]]
        |> declareTraversalReadings
    graph, root.Id, marker.Id, effect.Id

[<Theory>]
[<InlineData("absent")>]
[<InlineData("visited only")>]
[<InlineData("different scope")>]
[<InlineData("different path")>]
[<InlineData("different graph")>]
let ``unit demand requires successful completion at the actual child occurrence`` defect =
    let graph, root, marker, effect = unitFixture ()
    // The path-mismatch case uses a second actual parent of the same effect,
    // rather than declaring the attached effect to be a detached root.
    let alternate = node 7 (SemanticKind.Sequential [effect]) unitType [NodeId.value effect] None
    let graph =
        if defect = "different path" then
            { graph with Nodes = graph.Nodes.Add(alternate.Id, alternate) }
            |> declareTraversalReadings
        else graph
    let operands = MLIRAccumulator.empty ()
    let position = Zipper.create graph root |> require "Missing unit root" |> atChild marker
    let ctx = context graph position operands
    match defect with
    | "visited only" -> ctx.GlobalVisited.Value <- Set.singleton effect
    | "different scope" -> MLIRAccumulator.completeVoid (atChild effect position) (ref (ScopeContext.root ())) operands
    | "different path" ->
        let child = Zipper.create graph alternate.Id |> require "Missing alternate effect parent" |> atChild effect
        MLIRAccumulator.completeVoid child ctx.ScopeContext operands
    | "different graph" ->
        let other = { graph with DeclarationRoots = [] }
        let child = Zipper.create other root |> require "Missing other root" |> atChild marker |> atChild effect
        MLIRAccumulator.completeVoid child ctx.ScopeContext operands
    | _ -> ()
    let output = Alex.Witnesses.EagerWitness.nanopass.Witness ctx position.Focus
    match output.Result with TRError _ -> () | result -> failwithf "Unit result invented from %s: %A" defect result
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps

[<Fact>]
let ``actual unit store completes once before the eager marker returns canonical unit`` () =
    let initial = node 0 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let cell = node 1 (SemanticKind.Binding("cell", true, false, None)) boolType [0] None
    let target = node 2 (SemanticKind.VarRef("cell", Some cell.Id)) boolType [] None
    let value = node 3 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let store = node 4 (SemanticKind.Set(target.Id, value.Id)) unitType [2; 3] None
    let marker = node 5 (SemanticKind.EagerExpr store.Id) unitType [4] None
    let carriers = [boolean 0 [0; 6]; boolean 1 [1; 6]; boolean 2 [1; 2; 6]; boolean 3 [3; 6]]
    let published =
        revision ([initial; cell; target; value; store; marker] @ List.map domain [6; 7; 8; 9])
        |> withEdges
            [ structural 0 1 EdgeRole.Attached; edge [1] 2 EdgeClass.Reference EdgeRole.Definition 0
              structural 2 4 EdgeRole.AssignTarget; structural 3 4 EdgeRole.AssignValue
              structural 4 5 EdgeRole.Subject ]
            [demandEdge 5 4] carriers
        |> withData [4; 5; 6; 7; 8; 9]
        |> withNumeric carriers [0; 2; 3]
        |> withDemand [marker.Id, store.Id] [marker.Id, [demandRelation 5 4]]
    let graph =
        { published with
            Emission =
                { published.Emission with
                    Callable =
                        { published.Emission.Callable with
                            Symbols = Map.ofList [cell.Id, CallableSymbolName.RootBinding "cell"] } } }
    let graph = declareBindingReadings graph
    let accumulator = MLIRAccumulator.empty ()
    let cellType = TMemRefStatic(1, TInt(IntWidth 1))
    MLIRAccumulator.bindNode cell.Id (Arg 0) cellType accumulator
    let position = Zipper.create graph marker.Id |> require "Missing store marker"
    let ctx = context graph position accumulator
    ctx.TraversalVisited.Value <- Set.singleton cell.Id
    let witness ctx (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.Set _ -> Alex.Witnesses.MutableAssignmentWitness.nanopass.Witness ctx node
        | SemanticKind.VarRef _ -> Alex.Witnesses.VarRefWitness.nanopass.Witness ctx node
        | SemanticKind.Literal _ -> Alex.Witnesses.LiteralWitness.nanopass.Witness ctx node
        | SemanticKind.EagerExpr _ -> Alex.Witnesses.EagerWitness.nanopass.Witness ctx node
        | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    visitAllNodes witness ctx position.Focus ctx.TraversalVisited
    Assert.Empty accumulator.Errors
    Assert.True(MLIRAccumulator.completedVoid (atChild store.Id position) ctx.ScopeContext accumulator)
    let result, resultType = MLIRAccumulator.recallNode marker.Id accumulator |> require "Missing unit value after actual store"
    Assert.Equal(TInt(IntWidth 32), resultType)
    let operations = ScopeContext.getOps ctx.ScopeContext.Value
    Assert.Single(operations |> List.filter (function MLIROp.MemRefOp(MemRefOp.Store _) -> true | _ -> false)) |> ignore
    let declaration = MLIROp.FuncOp(FuncOp.FuncDef("eager_store", [Arg 0, cellType], [resultType],
        operations @ [MLIROp.FuncOp(FuncOp.Return [{ SSA = result; Type = resultType }])], FuncVisibility.Private))
    Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "eager_store" [declaration]
    |> Alex.Tests.Tools.mlirOpt ["--verify-each"] |> ignore

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``void Console call output remains in its eager conditional arm before unit completion`` active =
    // The component supplies an already admitted void Console ABI operation.
    // It tests completion/placement, not source platform admission or linking.
    let guard = node 0 (SemanticKind.Literal(NativeLiteral.Bool active)) boolType [] None
    let effect = node 1 (SemanticKind.PatternBinding "Console.writeln result") unitType [] None
    let marker = node 2 (SemanticKind.EagerExpr effect.Id) unitType [1] None
    let fallback = node 3 (SemanticKind.Literal NativeLiteral.Unit) unitType [] None
    let choice = node 4 (SemanticKind.IfThenElse(guard.Id, marker.Id, Some fallback.Id)) unitType [0; 2; 3] None
    let carriers = [boolean 0 [0; 5]]
    let graph =
        revision ([guard; effect; marker; fallback; choice] @ List.map domain [5; 6; 7; 8])
        |> withEdges
            [ structural 1 2 EdgeRole.Subject; structural 0 4 EdgeRole.Guard
              structural 2 4 EdgeRole.ThenBranch; structural 3 4 EdgeRole.ElseBranch ]
            [demandEdge 2 1] carriers
        |> withData [1; 2; 3; 4; 5; 6; 7; 8]
        |> withNumeric carriers [0]
        |> withDemand [marker.Id, effect.Id] [marker.Id, [demandRelation 2 1]]
        |> declareTraversalReadings
    let accumulator = MLIRAccumulator.empty ()
    let position = Zipper.create graph choice.Id |> require "Missing unit conditional"
    let ctx = context graph position accumulator
    let rec witness ctx (node: SemanticNode) =
        if node.Id = effect.Id then
            { InlineOps = [MLIROp.FuncOp(FuncOp.FuncCall([], "Console.writeln", []))]
              TopLevelOps = []; Result = TRVoid }
        else
            match node.Kind with
            | SemanticKind.IfThenElse _ -> (Alex.Witnesses.ControlFlowWitness.createNanopass (fun () -> witness)).Witness ctx node
            | SemanticKind.EagerExpr _ -> Alex.Witnesses.EagerWitness.nanopass.Witness ctx node
            | SemanticKind.Literal _ -> Alex.Witnesses.LiteralWitness.nanopass.Witness ctx node
            | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    visitAllNodes witness ctx position.Focus ctx.TraversalVisited
    Assert.Empty accumulator.Errors
    let operations = ScopeContext.getOps ctx.ScopeContext.Value
    let isCall = function MLIROp.FuncOp(FuncOp.FuncCall(_, "Console.writeln", _)) -> true | _ -> false
    Assert.DoesNotContain(operations, isCall)
    let yes, no = operations |> List.choose (function MLIROp.SCFOp(SCFOp.If(_, yes, Some no, _)) -> Some(yes, no) | _ -> None) |> Assert.Single
    Assert.Single(List.filter isCall yes) |> ignore
    Assert.DoesNotContain(no, isCall)
    Assert.True(yes |> List.exists (function MLIROp.ArithOp(ArithOp.ConstI(_, 0L, TInt(IntWidth 32))) -> true | _ -> false))
    let result, resultType = MLIRAccumulator.recallNode choice.Id accumulator |> require "Missing conditional unit"
    let declaration = MLIROp.FuncOp(FuncOp.FuncDef("eager_console", [], [resultType],
        operations @ [MLIROp.FuncOp(FuncOp.Return [{ SSA = result; Type = resultType }])], FuncVisibility.Private))
    let effectDeclaration = MLIROp.FuncOp(FuncOp.FuncDecl("Console.writeln", [], [], FuncVisibility.Private, []))
    Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "eager_console" [effectDeclaration; declaration]
    |> Alex.Tests.Tools.mlirOpt ["--verify-each"] |> ignore

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``failed void operand or subtree cannot acquire successful completion`` subtree =
    let graph, root, marker, effect = unitFixture ()
    let failure = NodeId((graph.Nodes.Keys |> Seq.map NodeId.value |> Seq.max) + 1)
    let graph =
        if subtree then
            let child = { graph.Nodes[effect] with Id = failure; Kind = SemanticKind.Literal NativeLiteral.Unit; Parent = Some effect; Children = [] }
            let container = { graph.Nodes[effect] with Kind = SemanticKind.Sequential [failure]; Children = [failure] }
            { graph with Nodes = graph.Nodes.Add(failure, child).Add(effect, container) }
        else graph
    let graph = declareTraversalReadings graph
    let accumulator = MLIRAccumulator.empty ()
    let position = Zipper.create graph root |> require "Missing unit root" |> atChild marker
    let ctx = context graph position accumulator
    let witness ctx (node: SemanticNode) =
        if node.Id = (if subtree then failure else effect) then WitnessOutput.error "actual effect failed"
        elif node.Id = effect then Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
        else Alex.Witnesses.EagerWitness.nanopass.Witness ctx node
    visitAllNodes witness ctx position.Focus ctx.TraversalVisited
    Assert.NotEmpty accumulator.Errors
    Assert.False(MLIRAccumulator.completedVoid (atChild effect position) ctx.ScopeContext accumulator)
    Assert.True((MLIRAccumulator.recallNode marker accumulator).IsNone)
    Assert.Empty(ScopeContext.getOps ctx.ScopeContext.Value)

[<Fact>]
let ``void completion follows complete operand scope snapshot restoration`` () =
    let graph, root, marker, effect = unitFixture ()
    let accumulator = MLIRAccumulator.empty ()
    let position = Zipper.create graph root |> require "Missing unit root" |> atChild marker
    let ctx = context graph position accumulator
    let child = atChild effect position
    MLIRAccumulator.completeVoid child ctx.ScopeContext accumulator
    let saved = MLIRAccumulator.snapshotOperands accumulator
    MLIRAccumulator.completeVoid child (ref (ScopeContext.root ())) accumulator
    Assert.False(MLIRAccumulator.completedVoid child ctx.ScopeContext accumulator)
    MLIRAccumulator.restoreOperands saved accumulator
    Assert.True(MLIRAccumulator.completedVoid child ctx.ScopeContext accumulator)
    MLIRAccumulator.bindNode effect (Arg 0) (TInt(IntWidth 32)) accumulator
    Assert.False(MLIRAccumulator.completedVoid child ctx.ScopeContext accumulator)
