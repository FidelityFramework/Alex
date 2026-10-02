module Alex.Tests.CallableFlowTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
module Operands = Alex.Traversal.CallableOperands
module Zipper = Alex.Traversal.PSGZipper

let private ok = function Result.Ok value -> value | Result.Error reason -> failwith reason

let private callbackType = functionFrom boolType boolType
let private higherType = functionFrom callbackType boolType
let private entryType = functionFrom unitType boolType
let private regular = LambdaContext.RegularClosure

/// The published boundary of one occurrence of a named callback.
let private callbackCarrier occurrence implementation argument result : CallableCarrier =
    { Occurrence = NodeId occurrence; SourceType = callbackType; Implementation = NodeId implementation
      Parameters = ["argument", boolType, NodeId argument]
      ParameterShapes = [CallableValueShape.Data(NodeId argument)]
      OmittedParameters = Set.empty
      Result = NodeId result; ResultShape = CallableValueShape.Data(NodeId result)
      Environment = None }

/// The published declaration of one named callback, read at its code.
let private callbackDeclaration implementation binding argument result name : CallableEmissionDeclaration =
    { Lookup = NodeId implementation; Implementation = NodeId implementation
      Parameters = ["argument", boolType, NodeId argument]; Result = NodeId result
      Context = regular; Captures = []
      Name = CallableSymbolName.RootBinding name
      Parent = Some(NodeId binding)
      Participants = Set.ofList [NodeId argument; NodeId result; NodeId implementation; NodeId binding] }

/// Both calls of the higher order function, as each flow row retains them.
let private calls : CallableFlowCall list =
    [ { Call = NodeId 17; Implementation = NodeId 14; Parameters = [NodeId 10]; Arguments = [NodeId 4]; Result = NodeId 13 }
      { Call = NodeId 19; Implementation = NodeId 14; Parameters = [NodeId 10]; Arguments = [NodeId 9]; Result = NodeId 13 } ]

let private flow occurrence dependencies : CallableFlow =
    { Occurrence = NodeId occurrence; SourceType = callbackType
      Alternatives = [NodeId 4; NodeId 9]
      Dependencies = dependencies |> List.map (fun (target, sources) -> NodeId target, List.map NodeId sources) |> Map.ofList
      Calls = calls }

/// Two named callbacks reach the one formal of a higher order function through
/// two calls. The nodes, the carriers, the flows and the projection rows are the
/// ones the compiler service publishes for this program. Rows of nodes that the
/// callable projection does not read here are left out.
let private fixture () =
    let nodes =
        [ node 0 (SemanticKind.PatternBinding "argument") boolType [] (Some 2)
          node 1 (SemanticKind.VarRef("argument", Some(NodeId 0))) boolType [] (Some 2)
          node 2 (SemanticKind.Lambda(["argument", boolType, NodeId 0], NodeId 1, [], None, regular)) callbackType [0; 1] (Some 3)
          node 3 (SemanticKind.Binding("first", false, false, None)) callbackType [2] None
          node 4 (SemanticKind.VarRef("first", Some(NodeId 3))) callbackType [] (Some 17)
          node 5 (SemanticKind.PatternBinding "argument") boolType [] (Some 7)
          node 6 (SemanticKind.VarRef("argument", Some(NodeId 5))) boolType [] (Some 7)
          node 7 (SemanticKind.Lambda(["argument", boolType, NodeId 5], NodeId 6, [], None, regular)) callbackType [5; 6] (Some 8)
          node 8 (SemanticKind.Binding("second", false, false, None)) callbackType [7] None
          node 9 (SemanticKind.VarRef("second", Some(NodeId 8))) callbackType [] (Some 19)
          node 10 (SemanticKind.PatternBinding "callback") callbackType [] (Some 14)
          node 11 (SemanticKind.VarRef("callback", Some(NodeId 10))) callbackType [] (Some 13)
          node 12 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] (Some 13)
          node 13 (SemanticKind.Application(NodeId 11, [NodeId 12])) boolType [11; 12] (Some 14)
          node 14 (SemanticKind.Lambda(["callback", callbackType, NodeId 10], NodeId 13, [], None, regular)) higherType [10; 13] (Some 15)
          node 15 (SemanticKind.Binding("higher", false, false, None)) higherType [14] None
          node 16 (SemanticKind.VarRef("higher", Some(NodeId 15))) higherType [] (Some 17)
          node 17 (SemanticKind.Application(NodeId 16, [NodeId 4])) boolType [16; 4] (Some 22)
          node 18 (SemanticKind.VarRef("higher", Some(NodeId 15))) higherType [] (Some 19)
          node 19 (SemanticKind.Application(NodeId 18, [NodeId 9])) boolType [18; 9] (Some 22)
          node 20 (SemanticKind.PatternBinding "opaque") callbackType [] None
          node 21 (SemanticKind.PatternBinding "unit") unitType [] (Some 23)
          node 22 (SemanticKind.Sequential [NodeId 17; NodeId 19]) boolType [17; 19] (Some 23)
          node 23 (SemanticKind.Lambda(["unit", unitType, NodeId 21], NodeId 22, [], None, regular)) entryType [21; 22] (Some 24)
          node 24 (SemanticKind.Binding("main", false, false, None)) entryType [23] None ]
    let carriers = Map.ofList [NodeId 4, callbackCarrier 4 2 0 1; NodeId 9, callbackCarrier 9 7 5 6]
    let flows = Map.ofList [NodeId 10, flow 10 [10, [4; 9]]; NodeId 11, flow 11 [10, [4; 9]; 11, [10]]]
    let data = [0; 1; 5; 6] |> List.map NodeId
    let callable =
        { Empty.callable with
            Carriers = carriers
            Flows = flows
            ValueShapes = data |> List.map (fun id -> id, CallableValueShape.Data id) |> Map.ofList
            SignatureData = Map.ofList [NodeId 2, Set.empty; NodeId 7, Set.empty]
            Transports =
                Map.ofList [NodeId 4, Set.ofList [NodeId 2; NodeId 3; NodeId 4]
                            NodeId 9, Set.ofList [NodeId 7; NodeId 8; NodeId 9]
                            NodeId 10, Set.ofList [NodeId 10]
                            NodeId 11, Set.ofList [NodeId 10; NodeId 11]]
            Declarations =
                Map.ofList [NodeId 2, callbackDeclaration 2 3 0 1 "first"
                            NodeId 7, callbackDeclaration 7 8 5 6 "second"]
            ClosedData = Set.ofList data }
    let numeric =
        { Empty.numeric with
            OccurrenceRepresentations =
                data |> List.map (fun id -> id, Ok(ValueRepresentation.Scalar SettledSlot.Bool)) |> Map.ofList }
    let revision =
        { revision nodes with
            Codata = { Codata.empty with CallableCarriers = carriers; CallableFlows = flows }
            Emission = { Empty.emission with Callable = callable; Numeric = numeric } }
        |> declareTraversalReadings
    revision, NodeId 10, NodeId 11, NodeId 4, NodeId 19, NodeId 20

let private context graph id bits =
    let operands = MLIRAccumulator.empty ()
    let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects bits; Accumulator = operands; RootAccumulator = operands
      ScopeContext = scope; RootScopeContext = scope; Graph = graph
      Zipper = Zipper.create graph id |> require "Missing formal occurrence"
      GlobalVisited = visited; TraversalVisited = visited }

[<Theory>]
[<InlineData(32)>]
[<InlineData(64)>]
let ``ordinary multi-target formal forwards its actual code operand through a verified indirect call`` bits =
    let graph, formal, alias, first, _, _ = fixture ()
    let ctx = context graph formal bits
    let shape = Operands.project ctx formal |> ok
    Assert.Equal(None, Operands.environmentType shape)
    let code = { SSA = Arg 0; Type = Operands.functionType shape }
    Operands.bind ctx formal code None |> ok
    Operands.copy ctx formal alias |> ok
    let actual = MLIRAccumulator.recallCallable alias ctx.Accumulator |> require "Alias lost callable operand"
    Assert.Equal(Arg 0, (Operands.code actual).SSA)
    Assert.Single(Operands.values actual) |> ignore
    Assert.True((MLIRAccumulator.recallNode alias ctx.Accumulator).IsNone)
    // A join cannot become one arbitrary alternative even though signatures match.
    match Operands.reproject ctx alias first with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "Callable flow was narrowed to a representative implementation"
    let boolean = TInt(IntWidth 1)
    let result = { SSA = V(501, 0); Type = boolean }
    let body = [MLIROp.FuncOp(FuncOp.FuncCallIndirect([result], code.SSA, [{ SSA = Arg 1; Type = boolean }]))
                MLIROp.FuncOp(FuncOp.Return [result])]
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("higher_order_flow", [Arg 0, code.Type; Arg 1, boolean], [boolean], body, FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok bits) "callable_flow" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.Contains("call_indirect", verified)
    Assert.DoesNotContain("unrealized_conversion_cast", verified)
    Assert.DoesNotContain("memref", verified)

[<Fact>]
let ``an added opaque actual retracts a previously projected formal on a new graph snapshot`` () =
    let graph, formal, alias, _, call, opaque = fixture ()
    Operands.project (context graph formal 64) formal |> ok |> ignore
    let node = graph.Nodes[call]
    let callee = match node.Kind with SemanticKind.Application(callee, _) -> callee | _ -> failwith "Missing fixture call"
    let changed = { node with Kind = SemanticKind.Application(callee, [opaque]); Children = [callee; opaque] }
    // For the changed program the compiler service refuses the flow row of the formal
    // and the flow row of its alias. The revision holds the changed call and neither row.
    let remaining (flows: Map<NodeId, CallableFlow>) = flows.Remove(formal).Remove(alias)
    let revised =
        { graph with
            Nodes = graph.Nodes.Add(call, changed)
            Codata = { graph.Codata with CallableFlows = remaining graph.Codata.CallableFlows }
            Emission =
                { graph.Emission with
                    Callable = { graph.Emission.Callable with Flows = remaining graph.Emission.Callable.Flows } } }
        |> declareTraversalReadings
    match Operands.project (context revised formal 64) formal with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "Stale complete callable flow survived the changed actual"
