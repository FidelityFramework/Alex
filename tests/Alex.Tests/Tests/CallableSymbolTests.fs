module Alex.Tests.CallableSymbolTests

open Xunit
open Fidelity.PSG
open Alex.CodeGeneration.CallableSymbols
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

type private Callable = { Binding: NodeId; Lambda: NodeId; Argument: NodeId; Reference: NodeId; Call: NodeId }

let private signature = functionFrom boolType boolType

/// One scope: a function spelled read and one call of it. The numbers start at
/// the base given, in the order the compiler service numbers the nodes.
let private scopeNodes b =
    [ node b (SemanticKind.PatternBinding "value") boolType [] (Some(b + 2))
      node (b + 1) (SemanticKind.VarRef("value", Some(NodeId b))) boolType [] (Some(b + 2))
      node (b + 2) (SemanticKind.Lambda(["value", boolType, NodeId b], NodeId(b + 1), [], None, LambdaContext.RegularClosure))
           signature [b; b + 1] (Some(b + 3))
      node (b + 3) (SemanticKind.Binding("read", false, false, None)) signature [b + 2] (Some(b + 7))
      node (b + 4) (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] (Some(b + 6))
      node (b + 5) (SemanticKind.VarRef("read", Some(NodeId(b + 3)))) signature [] (Some(b + 6))
      node (b + 6) (SemanticKind.Application(NodeId(b + 5), [NodeId(b + 4)])) boolType [b + 5; b + 4] (Some(b + 7))
      node (b + 7) (SemanticKind.Sequential [NodeId(b + 3); NodeId(b + 6)]) boolType [b + 3; b + 6] None ]

let private participants b = [NodeId b; NodeId(b + 1); NodeId(b + 2); NodeId(b + 3)] |> Set.ofList

let private carrier b occurrence : CallableCarrier =
    { Occurrence = NodeId occurrence; SourceType = signature; Implementation = NodeId(b + 2)
      Parameters = ["value", boolType, NodeId b]; ParameterShapes = [CallableValueShape.Data(NodeId b)]
      OmittedParameters = Set.empty
      Result = NodeId(b + 1); ResultShape = CallableValueShape.Data(NodeId(b + 1))
      Environment = None }

let private declaration b lookup parent : CallableEmissionDeclaration =
    { Lookup = NodeId lookup; Implementation = NodeId(b + 2)
      Parameters = ["value", boolType, NodeId b]; Result = NodeId(b + 1)
      Context = LambdaContext.RegularClosure; Captures = []
      Name = CallableSymbolName.LocalBinding(NodeId(b + 3), "read")
      Parent = Some(NodeId parent); Participants = participants b }

/// The published source call of one scope. A saturated call also names its binding.
let private call saturated b : CallableEmissionCall =
    { Site = NodeId(b + 6); Implementation = NodeId(b + 2)
      Parameters = ["value", boolType, NodeId b]; Arguments = [NodeId(b + 4)]; Result = NodeId(b + 1)
      SignatureData = Set.empty
      Participants =
        [b; b + 1; b + 2; b + 4; b + 5; b + 6] @ (if saturated then [b + 3] else [])
        |> List.map NodeId |> Set.ofList }

/// Resolved component inputs: two separate scopes deliberately use the same
/// source spelling. This does not reproduce name resolution or curry analysis.
/// The rows are the ones the compiler service publishes for these two scopes.
let private fixture saturated =
    let bases = [0; 8]
    let each rows = bases |> List.collect rows
    let data = each (fun b -> [b; b + 1; b + 4; b + 6; b + 7]) |> List.map NodeId
    let code = each (fun b -> [b + 2; b + 3; b + 5]) |> List.map NodeId
    let carriers = each (fun b -> [b + 2; b + 3; b + 5] |> List.map (fun id -> NodeId id, carrier b id)) |> Map.ofList
    let callable =
        { Empty.callable with
            Carriers = carriers
            ValueShapes =
                (data |> List.map (fun id -> id, CallableValueShape.Data id))
                @ (code |> List.map (fun id -> id, CallableValueShape.Callable id))
                |> Map.ofList
            SignatureData = each (fun b -> [NodeId(b + 2), Set.empty]) |> Map.ofList
            Calls = each (fun b -> [NodeId(b + 6), call saturated b]) |> Map.ofList
            Declarations =
                each (fun b -> [NodeId(b + 2), declaration b (b + 2) (b + 3)
                                NodeId(b + 3), declaration b (b + 3) (b + 7)]) |> Map.ofList
            Symbols =
                each (fun b -> [b + 2; b + 3] |> List.map (fun id -> NodeId id, CallableSymbolName.LocalBinding(NodeId(b + 3), "read")))
                |> Map.ofList
            DirectCallees = each (fun b -> [NodeId(b + 5), NodeId(b + 3)]) |> Map.ofList
            Arguments = each (fun b -> [NodeId(b + 2), Map.ofList [NodeId b, [0]]]) |> Map.ofList
            AliasTargets =
                each (fun b -> [b, b; b + 1, b; b + 2, b + 2; b + 3, b + 2; b + 4, b + 4; b + 5, b + 2; b + 6, b + 6; b + 7, b + 7])
                |> List.map (fun (occurrence, target) -> NodeId occurrence, NodeId target) |> Map.ofList
            ClosedData = Set.ofList data }
    let numeric =
        { Empty.numeric with
            OccurrenceRepresentations =
                data |> List.map (fun id -> id, Ok(ValueRepresentation.Scalar SettledSlot.Bool)) |> Map.ofList }
    let calls =
        if saturated then
            bases |> List.map (fun b -> NodeId(b + 6), { TargetBindingId = NodeId(b + 3); AllArgNodes = [NodeId(b + 4)] }) |> Map.ofList
        else Map.empty
    let graph =
        { revision (each scopeNodes) with
            Codata = { Codata.empty with CallableCarriers = carriers; Curry = { Codata.empty.Curry with SaturatedCalls = calls } }
            Emission = { Empty.emission with Callable = callable; Numeric = numeric } }
        |> declareTraversalReadings
    let functions =
        bases |> List.map (fun b ->
            { Binding = NodeId(b + 3); Lambda = NodeId(b + 2); Argument = NodeId(b + 4); Reference = NodeId(b + 5); Call = NodeId(b + 6) })
    graph, functions

let private withCallable change (graph: Revision) =
    { graph with Emission = { graph.Emission with Callable = change graph.Emission.Callable } }

/// The rows that name the code of one callable, restated for another published name.
let private namedCode name (fn: Callable) (graph: Revision) =
    graph |> withCallable (fun callable ->
        { callable with
            Symbols = callable.Symbols.Add(fn.Lambda, name)
            Declarations = callable.Declarations.Add(fn.Lambda, { callable.Declarations[fn.Lambda] with Name = name }) })

/// The rows that name one callable, restated for another published name. The
/// binding row also states the parent the binding has in that revision.
let private named name parent (fn: Callable) (graph: Revision) =
    graph |> namedCode name fn |> withCallable (fun callable ->
        { callable with
            Symbols = callable.Symbols.Add(fn.Binding, name)
            Declarations =
                callable.Declarations.Add(fn.Binding, { callable.Declarations[fn.Binding] with Name = name; Parent = parent }) })

let private context (graph: Revision) site operands =
    let rootScope = ref (ScopeContext.root ())
    let scope = ref (ScopeContext.createChild rootScope.Value FunctionLevel)
    let visited = ref Set.empty
    { Coeffects = coeffects 64
      Accumulator = operands; RootAccumulator = operands
      ScopeContext = scope; RootScopeContext = rootScope
      Graph = graph; Zipper = Zipper.create graph site |> require "Missing component site"
      GlobalVisited = visited; TraversalVisited = visited }

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``ordinary and saturated calls preserve resolved identity across equal local names`` saturated =
    let graph, functions = fixture saturated
    let symbols =
        functions |> List.map (fun fn ->
            let definitionSymbol = lambda graph graph.Nodes[fn.Lambda] false
            let operands = MLIRAccumulator.empty ()
            MLIRAccumulator.bindNode fn.Argument (Arg 0) (TInt(IntWidth 1)) operands
            let ctx = context graph fn.Call operands
            let output = Alex.Witnesses.ApplicationWitness.nanopass.Witness ctx graph.Nodes[fn.Call]
            match output.Result with
            | TRValue _ -> ()
            | other -> failwithf "Call was not witnessed: %A" other
            let targets = output.InlineOps |> List.choose (function MLIROp.FuncOp(FuncOp.FuncCall(_, target, _)) -> Some target | _ -> None)
            Assert.Equal(definitionSymbol, Assert.Single targets)
            Assert.Equal(Some definitionSymbol, tryBinding graph fn.Binding)
            Assert.Same(graph, ctx.Graph)
            Assert.Empty(ctx.TraversalVisited.Value)
            Assert.Empty(operands.Errors)
            definitionSymbol)
    Assert.NotEqual<string>(symbols[0], symbols[1])

[<Fact>]
let ``module and external spellings and anonymous closure identities are preserved`` () =
    let graph, functions = fixture false
    let fn = functions.Head
    let moduleNode = node 20 (SemanticKind.ModuleDef("Library", [fn.Binding])) unitType [] None
    let binding = graph.Nodes[fn.Binding]
    let moduleGraph =
        { graph with Nodes = graph.Nodes.Add(moduleNode.Id, moduleNode).Add(fn.Binding, { binding with Parent = Some moduleNode.Id }) }
        |> named (CallableSymbolName.ModuleBinding("Library", "read")) (Some moduleNode.Id) fn
        |> declareTraversalReadings
    Assert.Equal(Some "Library.read", tryBinding moduleGraph fn.Binding)
    Assert.Equal("Library.read", lambda moduleGraph moduleGraph.Nodes[fn.Lambda] false)
    Assert.Equal(Some "Library.read", tryBinding moduleGraph fn.Binding)
    let externalGraph =
        { graph with Nodes = graph.Nodes.Add(fn.Binding, { binding with Parent = None }) }
        |> named (CallableSymbolName.RootBinding "read") None fn
        |> declareTraversalReadings
    Assert.Equal(Some "read", tryBinding externalGraph fn.Binding)
    Assert.Equal("read", lambda externalGraph externalGraph.Nodes[fn.Lambda] false)
    // The contract states an anonymous code identity as one published name. It
    // holds no separate row for a lambda expression and for a closure pair.
    let original = graph.Nodes[fn.Lambda]
    let anonymousGraph = graph |> namedCode (CallableSymbolName.Anonymous fn.Lambda) fn
    Assert.Equal(sprintf "lambda_%d" (NodeId.value fn.Lambda), lambda anonymousGraph original true)

    // Native address plans are already settled by CCS. The witness retains that
    // symbol; this local-name projection does not re-resolve native entry plans.
    let addresses = Map.ofList [fn.Call, FunctionPointerPlan.Address("Library.read", fn.Lambda)]
    let addressGraph =
        { moduleGraph with
            Codata = { moduleGraph.Codata with FunctionPointers = addresses }
            Emission =
                { moduleGraph.Emission with
                    Callable = { moduleGraph.Emission.Callable with NativeEntries = Map.ofList [fn.Lambda, "Library.read"] } } }
    let ctx = context addressGraph fn.Call (MLIRAccumulator.empty ())
    let output = Alex.Witnesses.FunctionPointerWitness.nanopass.Witness ctx addressGraph.Nodes[fn.Call]
    match output.Result with
    | TRError reason -> Assert.Contains("native function address", reason.Message)
    | other -> failwithf "Native address was emitted without a target ABI contract: %A" other
    Assert.Empty output.InlineOps
