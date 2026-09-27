module Alex.Tests.ControlFlowOccurrenceTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

let private identities = List.map NodeId >> Set.ofList

/// The target node of one settled domain relation. The compiler service adds one for each
/// of the numeric, memory, spatial and boundary domains. It is a unit literal that is not reachable.
let private domainNode number =
    { node number (SemanticKind.Literal NativeLiteral.Unit) unitType [] None with IsReachable = false }

/// The carrier published for a bool occurrence, with the participants given.
let private boolCarrier site participants : ScalarCarrier =
    { Site = NodeId site
      Slot = SettledSlot.Bool
      Range = ValueRange.Bounded(0I, 1I)
      Representation = None
      Declaration = None
      SourceType = boolType
      Obligations = []
      Participants = identities participants }

/// The callable rows published for a fixture in which every occurrence is data.
/// Each alias row is a node and its endpoint. Each support row is a node and its support.
let private callableRows aliases units supports : CallableEmissionProjection =
    { Empty.callable with
        ValueShapes = aliases |> List.map (fun (site, _) -> NodeId site, CallableValueShape.Data(NodeId site)) |> Map.ofList
        AliasTargets = aliases |> List.map (fun (site, target) -> NodeId site, NodeId target) |> Map.ofList
        UnitNodes = identities units
        ClosedData = aliases |> List.map fst |> identities
        Supports = supports |> List.map (fun (site, support) -> NodeId site, identities support) |> Map.ofList }

/// The numeric rows published for a fixture in which every reachable occurrence is a bool.
let private numericRows (carriers: ScalarCarrier list) results : NumericWitnessProjection =
    let sites = carriers |> List.map _.Site
    { Empty.numeric with
        Values = carriers |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList
        Required = Set.ofList sites
        ResultSites = identities results
        SourceTypes = sites |> List.map (fun site -> site, boolType) |> Map.ofList
        OccurrenceRepresentations =
            sites |> List.map (fun site -> site, Ok(ValueRepresentation.Scalar SettledSlot.Bool)) |> Map.ofList
        TypeRepresentations = Map.ofList [ (boolType, Ok(ValueRepresentation.Scalar SettledSlot.Bool)) ] }

let private published nodes callable numeric =
    let stated = revision nodes
    { stated with Emission = { stated.Emission with Callable = callable; Numeric = numeric } }

[<Fact>]
let ``conditional guard descends through its actual occurrence and recalls the enclosing operand`` () =
    let formal = node 0 (SemanticKind.PatternBinding "condition") boolType [] None
    let read = node 1 (SemanticKind.VarRef("condition", Some formal.Id)) boolType [] None
    let guard = node 2 (SemanticKind.Sequential [read.Id]) boolType [1] None
    let yes = node 3 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let no = node 4 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let choice = node 5 (SemanticKind.IfThenElse(guard.Id, yes.Id, Some no.Id)) boolType [2; 3; 4] None
    let root = node 6 (SemanticKind.Sequential [choice.Id]) boolType [5] None
    let graph =
        published
            [formal; read; guard; yes; no; choice; root; domainNode 7; domainNode 8; domainNode 9; domainNode 10]
            (callableRows
                [0, 0; 1, 0; 2, 2; 3, 3; 4, 4; 5, 5; 6, 6; 7, 7; 8, 8; 9, 9; 10, 10]
                [7; 8; 9; 10]
                [0, [0]; 1, [0; 1]; 2, [2]; 3, [3]; 4, [4]; 5, [5]; 6, [6]; 7, [7]; 8, [8]; 9, [9]; 10, [10]])
            (numericRows
                [ boolCarrier 0 [0; 7]; boolCarrier 1 [0; 1; 7]; boolCarrier 2 [1; 2; 7]
                  boolCarrier 3 [3; 7]; boolCarrier 4 [4; 7]; boolCarrier 5 [2; 3; 4; 5; 7]
                  boolCarrier 6 [5; 6; 7] ]
                [1; 2; 3; 4; 5; 6])
    let accumulator = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode formal.Id (Arg 0) (TInt(IntWidth 1)) accumulator
    let scope = ref (ScopeContext.root ())
    let visited = ref (Set.singleton formal.Id)
    let position = Zipper.create graph root.Id |> require "Missing conditional root"
    let ctx =
        { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
          ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
          GlobalVisited = visited; TraversalVisited = visited }
    let reads = ResizeArray<NodeId list>()
    let rec witness ctx (node: SemanticNode) =
        Assert.Equal(node.Id, ctx.Zipper.Focus.Id)
        if node.Id = read.Id then
            let parent = Zipper.up ctx.Zipper |> require "Read lost its guard"
            let grandparent = Zipper.up parent |> require "Guard lost its conditional"
            reads.Add([parent.Focus.Id; grandparent.Focus.Id])
        match node.Kind with
        | SemanticKind.IfThenElse _ -> (Alex.Witnesses.ControlFlowWitness.createNanopass (fun () -> witness)).Witness ctx node
        | SemanticKind.VarRef _ -> Alex.Witnesses.VarRefWitness.nanopass.Witness ctx node
        | SemanticKind.Literal _ -> Alex.Witnesses.LiteralWitness.nanopass.Witness ctx node
        | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    visitAllNodes witness ctx position.Focus visited
    Assert.Empty accumulator.Errors
    Assert.Equal<NodeId list>([guard.Id; choice.Id], Assert.Single reads)
    Assert.Equal(Some(Arg 0, TInt(IntWidth 1)), MLIRAccumulator.recallNode read.Id accumulator)
    let result, resultType = MLIRAccumulator.recallNode root.Id accumulator |> require "Conditional lost its result"
    let operations = ScopeContext.getOps scope.Value
    let functionBody = operations @ [MLIROp.FuncOp(FuncOp.Return [{ SSA = result; Type = resultType }])]
    let declaration = MLIROp.FuncOp(FuncOp.FuncDef("conditional_occurrence", [Arg 0, TInt(IntWidth 1)], [resultType], functionBody, FuncVisibility.Private))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "conditional_occurrence" [declaration]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.Contains("scf.if %arg0", verified)

[<Fact>]
let ``control flow rejects a branch missing its declared occurrence even when an operand was recalled`` () =
    let guard = node 0 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let yes = node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let no = node 2 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    // The conditional names the then branch in its kind and omits it from its children.
    let choice = node 3 (SemanticKind.IfThenElse(guard.Id, yes.Id, Some no.Id)) boolType [0; 2] None
    let graph =
        published
            [guard; yes; no; choice; domainNode 4; domainNode 5; domainNode 6; domainNode 7]
            (callableRows
                [0, 0; 1, 1; 2, 2; 3, 3; 4, 4; 5, 5; 6, 6; 7, 7]
                [4; 5; 6; 7]
                [0, [0]; 1, [1]; 2, [2]; 3, [3]; 4, [4]; 5, [5]; 6, [6]; 7, [7]])
            (numericRows
                [ boolCarrier 0 [0; 4]; boolCarrier 1 [1; 4]; boolCarrier 2 [2; 4]
                  boolCarrier 3 [0; 1; 2; 3; 4] ]
                [0; 1; 2; 3])
    let accumulator = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode yes.Id (Arg 0) (TInt(IntWidth 1)) accumulator
    let scope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    let position = Zipper.create graph choice.Id |> require "Missing conditional root"
    let ctx =
        { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
          ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
          GlobalVisited = visited; TraversalVisited = visited }
    let rec witness ctx (node: SemanticNode) =
        Assert.NotEqual(yes.Id, node.Id)
        match node.Kind with
        | SemanticKind.IfThenElse _ -> (Alex.Witnesses.ControlFlowWitness.createNanopass (fun () -> witness)).Witness ctx node
        | SemanticKind.Literal _ -> Alex.Witnesses.LiteralWitness.nanopass.Witness ctx node
        | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    visitAllNodes witness ctx position.Focus visited
    Assert.NotEmpty accumulator.Errors
    Assert.DoesNotContain(yes.Id, visited.Value)
