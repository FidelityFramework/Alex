module Alex.Tests.CallableOperandTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
module Operands = Alex.Traversal.CallableOperands
module Zipper = Alex.Traversal.PSGZipper

let private ok = function Result.Ok value -> value | Result.Error reason -> failwith reason
let private failure = function Result.Error reason -> reason | Result.Ok _ -> failwith "Expected a rejected callable contract"
let private boolean = TInt(IntWidth 1)

type private Fixture = {
    Graph: Revision
    Owner: NodeId
    Alias: NodeId
    Other: NodeId
    Implementation: NodeId
    Formal: NodeId
}

let private sourceType = functionFrom boolType boolType
let private environmentType = arrayOf uint8Type
let private regular = LambdaContext.RegularClosure

let private ids numbers = List.map NodeId numbers
let private dataShapes numbers = ids numbers |> List.map (fun id -> id, CallableValueShape.Data id)
let private callableShapes numbers = ids numbers |> List.map (fun id -> id, CallableValueShape.Callable id)
let private represented form numbers = ids numbers |> List.map (fun id -> id, Ok form)
let private transports rows = rows |> List.map (fun (destination, sources) -> NodeId destination, Set.ofList (ids sources))
let private adding rows table = rows |> List.fold (fun held (key, value) -> Map.add key value held) table

let private flag = ValueRepresentation.Scalar SettledSlot.Bool
let private real = ValueRepresentation.Scalar(SettledSlot.Real 64)
/// The published form of the one byte environment at its formal.
let private environmentBytes = ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
/// The published form of a byte array that has no settled extent.
let private byteArray = ValueRepresentation.Buffer(None, ValueRepresentation.Scalar(SettledSlot.Integer(8, Some "uint8")))

let private withCodata change (graph: Revision) = { graph with Codata = change graph.Codata }
let private withCallable change (graph: Revision) =
    { graph with Emission = { graph.Emission with Callable = change graph.Emission.Callable } }
let private withNumeric change (graph: Revision) =
    { graph with Emission = { graph.Emission with Numeric = change graph.Emission.Numeric } }

/// The physical formals of the fixture code. A captured code takes its environment first.
let private formals captured argumentType =
    (if captured then ["environment", environmentType, NodeId 0] else []) @ ["argument", argumentType, NodeId 1]

/// The published boundary of one occurrence of the fixture code.
let private carrierOf captured argumentType source occurrence : CallableCarrier =
    let parameters = formals captured argumentType
    { Occurrence = NodeId occurrence; SourceType = source; Implementation = NodeId 4
      Parameters = parameters
      ParameterShapes = parameters |> List.map (fun (_, _, formal) -> CallableValueShape.Data formal)
      OmittedParameters = Set.empty
      Result = NodeId 3; ResultShape = CallableValueShape.Data(NodeId 3)
      Environment = if captured then Some { Owner = NodeId 5; Formal = NodeId 0 } else None }

/// One published declaration row of the fixture code.
let private declarationOf captured argumentType lookup name parent participants : CallableEmissionDeclaration =
    { Lookup = NodeId lookup; Implementation = NodeId 4
      Parameters = formals captured argumentType; Result = NodeId 3
      Context = regular; Captures = []
      Name = name; Parent = Option.map NodeId parent
      Participants = Set.ofList (ids participants) }

let private known = { Implementation = NodeId 4; EnvironmentOwner = NodeId 5 }

/// These are already settled component participants. They establish no source
/// residence proof; source admission and native execution remain separate gates.
/// The rows are the ones the compiler service publishes for these participants.
let private fixture captured =
    let nodes =
        [ node 0 (SemanticKind.PatternBinding "environment") environmentType [] None
          node 1 (SemanticKind.PatternBinding "argument") boolType [] None
          node 2 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
          node 3 (SemanticKind.VarRef("argument", Some(NodeId 1))) boolType [] None
          node 4 (SemanticKind.Lambda(formals captured boolType, NodeId 3, [], None, regular))
               (if captured then functionFrom environmentType sourceType else sourceType)
               (if captured then [0; 1; 3] else [1; 3]) None
          (if captured then node 5 (SemanticKind.ClosureValue(NodeId 4, NodeId 6)) sourceType [4; 6] None
           else node 5 (SemanticKind.Binding("plainCode", false, false, None)) sourceType [4] None)
          node 6 (SemanticKind.EnvironmentCreate(NodeId 5, [NodeId 2, NodeId 2])) environmentType [] None
          node 7 (SemanticKind.VarRef("first", Some(NodeId 5))) sourceType [] None
          node 8 (SemanticKind.VarRef("second", Some(NodeId 5))) sourceType [] None ]
    let slot: ContinuationSlot =
        { Source = NodeId 2; ValueType = boolType; IsCapture = true; Holds = CaptureSlotKind.Scalar SettledSlot.Bool
          Field = { Name = "capture"; Slot = SettledSlot.Bool; Offset = Some 0; Size = Some 1; Align = Some 1 } }
    let layout: EnvironmentLayout =
        { Owner = NodeId 5; Implementation = NodeId 4; Formal = NodeId 0
          Slots = [slot]; Bytes = 1; Alignment = 1; Obligations = [] }
    let carriers =
        (if captured then [5; 7; 8] else [4; 5; 7; 8])
        |> List.map (fun occurrence -> NodeId occurrence, carrierOf captured boolType sourceType occurrence) |> Map.ofList
    let reference target : Hyperedge =
        { Class = EdgeClass.Reference; Role = EdgeRole.Definition; Sources = [NodeId 5]; Target = NodeId target; Ordinal = 0 }
    let edges =
        [reference 7; reference 8] @
        (if captured then
            [{ Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentFormal
               Sources = [NodeId 5; NodeId 4]; Target = NodeId 0; Ordinal = 0 }
             { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentCapture false
               Sources = [NodeId 5; NodeId 2; NodeId 2]; Target = NodeId 6; Ordinal = 0 }]
         else [])
    let codata =
        if captured then
            { Codata.empty with
                CallableCarriers = carriers
                KnownCallables = ids [5; 7; 8] |> List.map (fun id -> id, known) |> Map.ofList
                EnvironmentLayouts = Map.ofList [NodeId 5, layout]
                EnvironmentOrigins = ids [0; 5; 7; 8] |> List.map (fun id -> id, NodeId 5) |> Map.ofList }
        else { Codata.empty with CallableCarriers = carriers }
    let callable =
        { Empty.callable with
            Carriers = carriers
            ValueShapes = dataShapes [0; 1; 2; 3; 6] @ callableShapes [4; 5; 7; 8] |> Map.ofList
            SignatureData = Map.ofList [NodeId 4, Set.empty]
            Transports =
                (if captured then transports [5, [5]; 7, [5; 7]; 8, [5; 8]]
                 else transports [4, [4]; 5, [4; 5]; 7, [4; 5; 7]; 8, [4; 5; 8]]) |> Map.ofList
            Declarations =
                (if captured then
                    [NodeId 4, declarationOf true boolType 4 (CallableSymbolName.Anonymous(NodeId 4)) None [0; 1; 3; 4]]
                 else
                    [NodeId 4, declarationOf false boolType 4 (CallableSymbolName.Anonymous(NodeId 4)) None [1; 3; 4]
                     NodeId 5, declarationOf false boolType 5 (CallableSymbolName.RootBinding "plainCode") None [1; 3; 4; 5]])
                |> Map.ofList
            ClosedData = Set.ofList (ids [0; 1; 2; 3; 6]) }
    let numeric =
        { Empty.numeric with
            OccurrenceRepresentations =
                represented (if captured then environmentBytes else byteArray) [0]
                @ represented flag [1; 2; 3] @ represented byteArray [6] |> Map.ofList }
    { Graph =
        { revision nodes with
            Edges = edges
            Codata = codata
            Emission = { Empty.emission with Callable = callable; Numeric = numeric } }
        |> declareTraversalReadings
      Owner = NodeId 5; Alias = NodeId 7; Other = NodeId 8
      Implementation = NodeId 4; Formal = NodeId 0 }

let private context graph occurrence =
    let accumulator = MLIRAccumulator.empty ()
    let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
      ScopeContext = scope; RootScopeContext = scope; Graph = graph
      Zipper = Zipper.create graph occurrence |> require "Missing callable occurrence"
      GlobalVisited = visited; TraversalVisited = visited }

let private code shape ssa : Val = { SSA = ssa; Type = Operands.functionType shape }
let private environment shape ssa : Val =
    { SSA = ssa; Type = Operands.environmentType shape |> require "No environment in captured fixture" }
let private heldEnvironment value = Operands.environment value |> require "Captured operand lost its environment"

[<Fact>]
let ``callable signature reads settled boundary representations without participant bodies`` () =
    let fixture = fixture false
    // These formals/results belong to another demanded scope. Their published
    // signature and representation rows remain authoritative component inputs.
    let graph = { fixture.Graph with Nodes = fixture.Graph.Nodes.Remove(NodeId 1).Remove(NodeId 3) }
    let ctx = context graph fixture.Owner
    let shape = Operands.project ctx fixture.Owner |> ok
    Assert.Equal<MLIRType>(TFunc([boolean], [boolean]), Operands.functionType shape)
    Assert.Empty ctx.Accumulator.AllOps
    Assert.True((MLIRAccumulator.recallNode fixture.Owner ctx.Accumulator).IsNone)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``callable signature refuses missing or unresolved boundary representation with no operands`` unresolved =
    let fixture = fixture false
    let representations = fixture.Graph.Emission.Numeric.OccurrenceRepresentations.Remove(NodeId 1)
    let representations =
        if unresolved then representations.Add(NodeId 1, Result.Error "source boundary remains unresolved") else representations
    let graph = fixture.Graph |> withNumeric (fun numeric -> { numeric with OccurrenceRepresentations = representations })
    let ctx = context graph fixture.Owner
    let reason = Operands.project ctx fixture.Owner |> failure
    Assert.Contains("Callable signature data participant 1", reason)
    Assert.Contains("source-published physical representation", reason)
    if unresolved then Assert.Contains("source boundary remains unresolved", reason)
    Assert.Empty ctx.Accumulator.AllOps
    Assert.True((MLIRAccumulator.recallNode fixture.Owner ctx.Accumulator).IsNone)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``lazy thunk declaration reads its settled symbol without an implementation body`` missingSymbol =
    let fixture = fixture false
    let graph = fixture.Graph |> withCallable (fun callable ->
        { callable with
            Declarations = callable.Declarations.Add(fixture.Implementation,
                { callable.Declarations[fixture.Implementation] with Context = LambdaContext.LazyThunk })
            Symbols =
                if missingSymbol then Map.empty
                else Map.ofList [fixture.Implementation, CallableSymbolName.Anonymous fixture.Implementation] })
    let graph = { graph with Nodes = graph.Nodes.Remove(fixture.Implementation).Remove(NodeId 1).Remove(NodeId 3) }
    let ctx = context graph fixture.Owner
    match Operands.thunkDeclaration ctx fixture.Implementation with
    | Ok(Some(symbol, _, body)) when not missingSymbol ->
        Assert.Equal("lambda_4", symbol)
        Assert.Equal(NodeId 3, body)
    | Result.Error reason when missingSymbol -> Assert.Contains("source-published declaration symbol for code 4", reason)
    | other -> failwithf "Unexpected source declaration reading: %A" other
    Assert.Empty ctx.Accumulator.AllOps

[<Fact>]
let ``returned closure preserves its own witnessed code and actual environment`` () =
    let fixture = fixture true
    let ctx = context fixture.Graph fixture.Owner
    let shape = Operands.project ctx fixture.Owner |> ok
    let codeValue = code shape (Arg 7)
    let environmentValue = environment shape (Arg 9)
    Operands.bind ctx fixture.Owner codeValue (Some environmentValue) |> ok
    let returned = Operands.reproject ctx fixture.Owner fixture.Owner |> ok
    Assert.Equal(codeValue, Operands.code returned)
    Assert.Equal(environmentValue, heldEnvironment returned)
    Assert.Empty ctx.Accumulator.Errors

[<Fact>]
let ``same code with different environments survives recall and alias copy without a scalar fallback`` () =
    let fixture = fixture true
    // This copy really forwards the second occurrence. Merely sharing its code
    // and environment schema would not establish that source relationship.
    let alias = { fixture.Graph.Nodes[fixture.Alias] with Kind = SemanticKind.VarRef("second", Some fixture.Other) }
    let edges = fixture.Graph.Edges |> List.map (fun edge ->
        if edge.Target = fixture.Alias && edge.Role = EdgeRole.Definition then { edge with Sources = [fixture.Other] }
        else edge)
    // The compiler service publishes the second occurrence on the transport path of this alias.
    let graph =
        { fixture.Graph with Nodes = fixture.Graph.Nodes.Add(fixture.Alias, alias); Edges = edges }
        |> withCallable (fun callable ->
            { callable with Transports = callable.Transports.Add(fixture.Alias, Set.ofList [fixture.Owner; fixture.Alias; fixture.Other]) })
    let ctx = context graph fixture.Owner
    let shape = Operands.project ctx fixture.Owner |> ok
    let fn = code shape (Arg 0)
    Operands.bind ctx fixture.Owner fn (Some(environment shape (Arg 1))) |> ok
    Operands.bind ctx fixture.Other fn (Some(environment shape (Arg 2))) |> ok
    Operands.copy ctx fixture.Other fixture.Alias |> ok
    let recalled id = MLIRAccumulator.recallCallable id ctx.Accumulator |> require "Callable pair was lost"
    Assert.Equal(Arg 1, (heldEnvironment (recalled fixture.Owner)).SSA)
    Assert.Equal(Arg 2, (heldEnvironment (recalled fixture.Alias)).SSA)
    Assert.Equal(Arg 0, (Operands.code (recalled fixture.Alias)).SSA)
    Assert.True((MLIRAccumulator.recallNode fixture.Alias ctx.Accumulator).IsNone)
    Assert.Equal(Some fn.Type, MLIRAccumulator.recallSSAType fn.SSA ctx.Accumulator)

[<Fact>]
let ``equal code and environment schema cannot authorize copying an unrelated source occurrence`` () =
    let fixture = fixture true
    let ctx = context fixture.Graph fixture.Owner
    let shape = Operands.project ctx fixture.Other |> ok
    Operands.bind ctx fixture.Other (code shape (Arg 0)) (Some(environment shape (Arg 2))) |> ok
    Operands.reproject ctx fixture.Other fixture.Alias |> failure |> ignore
    Assert.True((MLIRAccumulator.recallCallable fixture.Alias ctx.Accumulator).IsNone)
    Assert.Equal(Arg 2, (heldEnvironment (MLIRAccumulator.recallCallable fixture.Other ctx.Accumulator).Value).SSA)

[<Fact>]
let ``operation scope restore keeps callable pairs and physical SSA types together`` () =
    let fixture = fixture true
    let ctx = context fixture.Graph fixture.Owner
    let shape = Operands.project ctx fixture.Owner |> ok
    Operands.bind ctx fixture.Owner (code shape (Arg 0)) (Some(environment shape (Arg 1))) |> ok
    let outer = MLIRAccumulator.snapshotOperands ctx.Accumulator
    Operands.bind ctx fixture.Owner (code shape (V(900, 0))) (Some(environment shape (V(900, 1)))) |> ok
    Operands.copy ctx fixture.Owner fixture.Alias |> ok
    MLIRAccumulator.restoreOperands outer ctx.Accumulator
    Assert.Same(outer.Callables, ctx.Accumulator.CallableAssoc)
    Assert.Same(outer.Scalars, ctx.Accumulator.NodeAssoc)
    Assert.Same(outer.Types, ctx.Accumulator.SSATypes)
    Assert.True((MLIRAccumulator.recallCallable fixture.Alias ctx.Accumulator).IsNone)
    Assert.True((MLIRAccumulator.recallSSAType (V(900, 1)) ctx.Accumulator).IsNone)
    Assert.Equal(Arg 1, (heldEnvironment (MLIRAccumulator.recallCallable fixture.Owner ctx.Accumulator).Value).SSA)

[<Fact>]
let ``code-only callable rejects an invented environment and captured callable rejects scalar packing`` () =
    let plain = fixture false
    let ctx = context plain.Graph plain.Owner
    let shape = Operands.project ctx plain.Owner |> ok
    let fn = code shape (Arg 0)
    Operands.bind ctx plain.Owner fn None |> ok
    Assert.Single(Operands.values (MLIRAccumulator.recallCallable plain.Owner ctx.Accumulator).Value) |> ignore
    Operands.bind ctx plain.Owner fn (Some { SSA = Arg 1; Type = TMemRefStatic(0, TInt(IntWidth 8)) })
    |> failure |> ignore
    let captured = fixture true
    let ctx = context captured.Graph captured.Owner
    let shape = Operands.project ctx captured.Owner |> ok
    Operands.bind ctx captured.Owner { SSA = Arg 0; Type = TMemRefStatic(2, TIndex) } (Some(environment shape (Arg 1)))
    |> failure |> ignore
    Assert.Empty ctx.Accumulator.CallableAssoc
    Assert.Empty ctx.Accumulator.SSATypes

[<Fact>]
let ``callable component yields code and matching environment together through standard structured control`` () =
    let fixture = fixture true
    let ctx = context fixture.Graph fixture.Owner
    let shape = Operands.project ctx fixture.Owner |> ok
    let left = Operands.create shape (code shape (Arg 1)) (Some(environment shape (Arg 2))) |> ok
    let right = Operands.create shape (code shape (Arg 3)) (Some(environment shape (Arg 4))) |> ok
    let selected = Operands.create shape (code shape (V(901, 0))) (Some(environment shape (V(901, 1)))) |> ok
    let parser = Alex.Patterns.ControlFlowPatterns.pBuildIndexSwitch
                    { SSA = Arg 0; Type = TIndex } [0L, ([], Operands.values left)]
                    ([], Operands.values right) (Operands.values selected)
    let operations = match matchAt parser ctx.Zipper 64 ctx.Accumulator with Result.Ok(operations, _) -> operations | Result.Error reason -> failwith reason
    let result = { SSA = V(901, 2); Type = boolean }
    let call = MLIROp.FuncOp(FuncOp.FuncCallIndirect([result], (Operands.code selected).SSA,
                    [heldEnvironment selected; { SSA = Arg 5; Type = boolean }]))
    let parameters = [Arg 0, TIndex; Arg 1, (Operands.code left).Type; Arg 2, (heldEnvironment left).Type
                      Arg 3, (Operands.code right).Type; Arg 4, (heldEnvironment right).Type; Arg 5, boolean]
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("callable_selection_component", parameters, [boolean],
                        operations @ [call; MLIROp.FuncOp(FuncOp.Return [result])], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "callable_selection" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.Contains("call_indirect", verified)
    Assert.DoesNotContain("unrealized_conversion_cast", verified)
    Assert.DoesNotContain("memref<2xindex>", verified)

/// A function that takes the fixture callable as its formal, or one that returns it.
/// The compiler service publishes these rows for three of the four fixtures. It
/// refuses to prepare the captured fixture that takes the callable. That fixture
/// states the carriers its settlement step derives and, for the same nodes, the
/// rows published for the other three.
let private higherOrder captured returnsCallable =
    let fixture = fixture captured
    let graph = fixture.Graph
    let callableType = graph.Nodes[fixture.Owner].Type
    let parameterType = if returnsCallable then boolType else callableType
    let resultType = if returnsCallable then callableType else boolType
    let ty = functionFrom parameterType resultType
    let implementation, binding, callable = if returnsCallable then 15, 16, 14 else 17, 18, 13
    let body = if returnsCallable then 14 else 16
    let parameters = ["input", parameterType, NodeId 13]
    let higher occurrence : CallableCarrier =
        { Occurrence = NodeId occurrence; SourceType = ty; Implementation = NodeId implementation
          Parameters = parameters
          ParameterShapes = [(if returnsCallable then CallableValueShape.Data else CallableValueShape.Callable) (NodeId 13)]
          OmittedParameters = Set.empty
          Result = NodeId body
          ResultShape = (if returnsCallable then CallableValueShape.Callable else CallableValueShape.Data) (NodeId body)
          Environment = None }
    let declared lookup name parent participants : CallableEmissionDeclaration =
        { Lookup = NodeId lookup; Implementation = NodeId implementation
          Parameters = parameters; Result = NodeId body
          Context = regular; Captures = []
          Name = name; Parent = Option.map NodeId parent
          Participants = Set.ofList (ids participants) }
    let inherited occurrence = NodeId occurrence, carrierOf captured boolType sourceType occurrence
    let nodes, carriers, shapes, paths, declarations, closed, forms =
        if returnsCallable then
            [ node 13 (SemanticKind.PatternBinding "input") parameterType [] None
              node 14 (SemanticKind.VarRef("returned", Some fixture.Owner)) callableType [] None
              node 15 (SemanticKind.Lambda(parameters, NodeId 14, [], None, regular)) ty [13; 14] None
              node 16 (SemanticKind.Binding("higher", false, false, None)) ty [15] None ],
            [ inherited 14; NodeId 15, higher 15; NodeId 16, higher 16 ],
            dataShapes [13] @ callableShapes [14; 15; 16],
            transports [14, (if captured then [5; 14] else [4; 5; 14]); 15, [15]; 16, [15; 16]],
            [ NodeId 15, declared 15 (CallableSymbolName.Anonymous(NodeId 15)) None [13; 14; 15]
              NodeId 16, declared 16 (CallableSymbolName.RootBinding "higher") None [13; 14; 15; 16] ],
            [13],
            represented flag [13]
        else
            // The startup and demand steps of the compiler service set the parents of the
            // fixture code. The owner is then an argument of the call, and a binding
            // that a call holds is published under a local name.
            [ { graph.Nodes[NodeId 1] with Parent = Some(NodeId 4) }
              { graph.Nodes[NodeId 3] with Parent = Some(NodeId 4) }
              { graph.Nodes[NodeId 4] with Parent = Some(NodeId 5) }
              { graph.Nodes[NodeId 5] with Parent = Some(NodeId 20) }
              node 13 (SemanticKind.PatternBinding "input") parameterType [] (Some 17)
              // This fixture tests transported callable components. Make its
              // formal genuinely demanded; an unused argument is lawfully omitted.
              node 14 (SemanticKind.VarRef("input", Some(NodeId 13))) callableType [] (Some 16)
              node 15 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] (Some 16)
              node 16 (SemanticKind.Application(NodeId 14, [NodeId 15])) boolType [14; 15] (Some 17)
              node 17 (SemanticKind.Lambda(parameters, NodeId 16, [], None, regular)) ty [13; 16] (Some 18)
              node 18 (SemanticKind.Binding("higher", false, false, None)) ty [17] None
              // A formal may inherit an actual's carrier only through complete
              // internal ingress rooted in a real startup activation.
              node 19 (SemanticKind.VarRef("higher", Some(NodeId 18))) ty [] (Some 20)
              node 20 (SemanticKind.Application(NodeId 19, [fixture.Owner])) boolType [19; 5] (Some 22)
              node 21 (SemanticKind.PatternBinding "unit") unitType [] (Some 22)
              node 22 (SemanticKind.Lambda(["unit", unitType, NodeId 21], NodeId 20, [], None, regular))
                   (functionFrom unitType boolType) [21; 20] (Some 23)
              node 23 (SemanticKind.Binding("main", false, false, None)) (functionFrom unitType boolType) [22] None ]
            @ (if captured then
                [ { graph.Nodes[NodeId 0] with Parent = Some(NodeId 4) }
                  { graph.Nodes[NodeId 6] with Parent = Some(NodeId 5) } ]
               else []),
            [ inherited 13 ] @ (if captured then [] else [ inherited 14 ])
            @ [ NodeId 17, higher 17; NodeId 18, higher 18; NodeId 19, higher 19 ],
            callableShapes [13; 14; 17; 18; 19] @ dataShapes [15; 16; 20; 21],
            transports ([13, [13]] @ (if captured then [] else [14, [13; 14]]) @ [17, [17]; 18, [17; 18]; 19, [17; 18; 19]]),
            (if captured then
                [ NodeId 4, declarationOf true boolType 4 (CallableSymbolName.Anonymous(NodeId 4)) (Some 5) [0; 1; 3; 4; 5] ]
             else
                [ NodeId 4, declarationOf false boolType 4 (CallableSymbolName.LocalBinding(NodeId 5, "plainCode")) (Some 5) [1; 3; 4; 5]
                  NodeId 5, declarationOf false boolType 5 (CallableSymbolName.LocalBinding(NodeId 5, "plainCode")) (Some 20) [1; 3; 4; 5] ])
            @ [ NodeId 17, declared 17 (CallableSymbolName.RootBinding "higher") (Some 18) [13; 16; 17; 18]
                NodeId 18, declared 18 (CallableSymbolName.RootBinding "higher") None [13; 16; 17; 18] ],
            [15; 16; 20; 21],
            represented flag [15; 16; 20] @ represented (ValueRepresentation.Scalar SettledSlot.Unit) [21]
    let revised =
        { graph with Nodes = nodes |> List.fold (fun held changed -> Map.add changed.Id changed held) graph.Nodes }
        |> withCodata (fun codata ->
            { codata with
                CallableCarriers = adding carriers codata.CallableCarriers
                KnownCallables = if captured then codata.KnownCallables.Add(NodeId callable, known) else codata.KnownCallables
                EnvironmentOrigins =
                    if captured then codata.EnvironmentOrigins.Add(NodeId callable, fixture.Owner) else codata.EnvironmentOrigins })
        |> withCallable (fun held ->
            { held with
                Carriers = adding carriers held.Carriers
                ValueShapes = adding shapes held.ValueShapes
                SignatureData = held.SignatureData.Add(NodeId implementation, Set.empty)
                Transports = adding paths held.Transports
                Declarations = adding declarations held.Declarations
                ClosedData = Set.union held.ClosedData (Set.ofList (ids closed)) })
        |> withNumeric (fun held -> { held with OccurrenceRepresentations = adding forms held.OccurrenceRepresentations })
        |> declareTraversalReadings
    revised, NodeId binding, NodeId callable, fixture.Owner

/// The same revision without the carrier row of one occurrence.
let private withoutCarrier occurrence graph =
    graph
    |> withCodata (fun codata -> { codata with CallableCarriers = codata.CallableCarriers.Remove occurrence })
    |> withCallable (fun callable -> { callable with Carriers = callable.Carriers.Remove occurrence })

/// The same revision with the carrier row of one occurrence stated as given.
let private withCarrier occurrence carrier graph =
    graph
    |> withCodata (fun codata -> { codata with CallableCarriers = codata.CallableCarriers.Add(occurrence, carrier) })
    |> withCallable (fun callable -> { callable with Carriers = callable.Carriers.Add(occurrence, carrier) })

[<Theory>]
[<InlineData(false, false)>]
[<InlineData(true, false)>]
[<InlineData(false, true)>]
[<InlineData(true, true)>]
let ``higher order and returned values expand only their settled callable components`` captured returnsCallable =
    let graph, binding, callable, original = higherOrder captured returnsCallable
    let ctx = context graph binding
    let shape = Operands.project ctx binding |> ok
    let held = Operands.project ctx original |> ok
    let components = Operands.functionType held :: (Operands.environmentType held |> Option.toList)
    if returnsCallable then
        Assert.Equal<MLIRType list>(components, Operands.resultTypes shape)
        Assert.Equal<MLIRType list list>([[boolean]], Operands.parameterTypes shape)
        Assert.Equal(CallableValueShape.Callable callable, graph.Codata.CallableCarriers[binding].ResultShape)
    else
        Assert.Equal<MLIRType list list>([components], Operands.parameterTypes shape)
        Assert.Equal<MLIRType list>([boolean], Operands.resultTypes shape)
        Assert.Equal<CallableValueShape list>([CallableValueShape.Callable callable], graph.Codata.CallableCarriers[binding].ParameterShapes)
    let missing = graph |> withoutCarrier callable
    let reason = Operands.project (context missing binding) binding |> failure
    Assert.Contains("Callable occurrence has no settled carrier contract.", reason)

[<Fact>]
let ``equal physical shapes cannot change the settled callable identity during copy`` () =
    let fixture = fixture false
    let original = fixture.Graph.Nodes[fixture.Implementation]
    let replacement = { original with Id = NodeId 13 }
    let alien = { fixture.Graph.Codata.CallableCarriers[fixture.Other] with Implementation = replacement.Id }
    // The replacement is a second code of the same physical shape. Its declaration
    // rows are the ones published for the original code, stated at its own identity.
    let declaration =
        { fixture.Graph.Emission.Callable.Declarations[fixture.Implementation] with
            Lookup = replacement.Id; Implementation = replacement.Id
            Name = CallableSymbolName.Anonymous replacement.Id
            Participants = Set.ofList [NodeId 1; NodeId 3; replacement.Id] }
    let graph =
        { fixture.Graph with Nodes = fixture.Graph.Nodes.Add(replacement.Id, replacement) }
        |> withCarrier fixture.Other alien
        |> withCallable (fun callable ->
            { callable with
                ValueShapes = callable.ValueShapes.Add(replacement.Id, CallableValueShape.Callable replacement.Id)
                SignatureData = callable.SignatureData.Add(replacement.Id, Set.empty)
                Declarations = callable.Declarations.Add(replacement.Id, declaration) })
    let originalContext = context fixture.Graph fixture.Owner
    let shape = Operands.project originalContext fixture.Owner |> ok
    Operands.bind originalContext fixture.Owner (code shape (Arg 0)) None |> ok
    let ctx = { context graph fixture.Owner with Accumulator = originalContext.Accumulator; RootAccumulator = originalContext.Accumulator }
    Operands.copy ctx fixture.Owner fixture.Other |> failure |> ignore
    Assert.True((MLIRAccumulator.recallCallable fixture.Other ctx.Accumulator).IsNone)

[<Fact>]
let ``cyclic callable signature references fail without recursive emission or a scalar substitute`` () =
    let graph, binding, input, _ = higherOrder false false
    let source = graph.Codata.CallableCarriers[binding]
    let cyclic = { source with Occurrence = input; SourceType = graph.Nodes[input].Type }
    let graph = graph |> withCarrier input cyclic
    let ctx = context graph binding
    let reason = Operands.project ctx binding |> failure
    Assert.Contains("Callable signature contains an unresolved recursive component reference.", reason)
    Assert.Empty ctx.Accumulator.AllOps
    Assert.Empty ctx.Accumulator.NodeAssoc
    Assert.Empty ctx.Accumulator.CallableAssoc

/// Component fixture for a checker-quantified, representation-neutral measure.
/// The code and capture layout stay shared; each alias retains its exact unit.
/// The contract holds the quantification as the signature permission of the code.
let private measuredFixture () =
    let existing = fixture true
    let graph = existing.Graph
    let variable: MeasureVar = { Id = 0; Name = Some "u" }
    let measure: Dimension = { Bases = Map.empty; Vars = Map.ofList [variable, 1] }
    let carrier = match floatType with TypeIdentity.Numeric(carrier, _) -> carrier | _ -> failwith "Expected a numeric float identity"
    let measured dimension = TypeIdentity.Numeric(carrier, dimension)
    let functionOf dimension = functionFrom (measured dimension) (measured dimension)
    let genericType = functionOf measure
    let declarationId = NodeId 13
    let code = graph.Nodes[existing.Implementation]
    let parameters, body =
        match code.Kind with
        | SemanticKind.Lambda(parameters, body, [], _, _) -> parameters, body
        | _ -> failwith "Expected fixture code"
    let name, _, argument = List.last parameters
    let parameters = [List.head parameters; name, measured measure, argument]
    let code =
        { code with Kind = SemanticKind.Lambda(parameters, body, [], None, regular)
                    Type = functionFrom graph.Nodes[existing.Formal].Type genericType }
    let owner = { graph.Nodes[existing.Owner] with Type = genericType; Parent = Some declarationId }
    let declaration =
        { owner with Id = declarationId; Kind = SemanticKind.Binding("measured", false, false, None)
                     Parent = None; Children = [owner.Id] }
    let unitOf unitName : Dimension = { Bases = Map.ofList [{ Name = unitName; Module = ["Fixture"] }, 1]; Vars = Map.empty }
    let alias id unitName =
        { graph.Nodes[id] with Kind = SemanticKind.VarRef("measured", Some declarationId); Type = functionOf (unitOf unitName) }
    let nodes =
        graph.Nodes.Add(code.Id, code).Add(owner.Id, owner).Add(declarationId, declaration)
            .Add(argument, { graph.Nodes[argument] with Type = measured measure })
            .Add(body, { graph.Nodes[body] with Type = measured measure })
            .Add(existing.Alias, alias existing.Alias "m")
            .Add(existing.Other, alias existing.Other "s")
    let carriers =
        [ 5, genericType; 7, functionOf (unitOf "m"); 8, functionOf (unitOf "s"); 13, genericType ]
        |> List.map (fun (occurrence, source) -> NodeId occurrence, carrierOf true (measured measure) source occurrence)
        |> Map.ofList
    let edges = graph.Edges |> List.map (fun edge ->
        if edge.Role = EdgeRole.Definition then { edge with Sources = [declarationId] } else edge)
    let measuredGraph =
        { graph with Nodes = nodes; Edges = edges }
        |> withCodata (fun codata ->
            { codata with
                CallableCarriers = carriers
                KnownCallables = codata.KnownCallables.Add(declarationId, codata.KnownCallables[owner.Id])
                EnvironmentOrigins = codata.EnvironmentOrigins.Add(declarationId, owner.Id) })
        |> withCallable (fun callable ->
            { callable with
                Carriers = carriers
                ValueShapes = callable.ValueShapes.Add(declarationId, CallableValueShape.Callable declarationId)
                SignatureData = Map.ofList [code.Id, Set.ofList [existing.Formal; argument; body]]
                Transports = transports [5, [5; 13]; 7, [5; 7; 13]; 8, [5; 8; 13]; 13, [5; 13]] |> Map.ofList
                Declarations =
                    Map.ofList [code.Id, declarationOf true (measured measure) 4 (CallableSymbolName.Anonymous code.Id) None [0; 1; 3; 4]]
                ClosedData = Set.ofList (ids [0; 2; 6]) })
        |> withNumeric (fun numeric ->
            { numeric with OccurrenceRepresentations = adding (represented real [1; 3]) numeric.OccurrenceRepresentations })
        |> declareTraversalReadings
    measuredGraph, declarationId, existing.Alias, existing.Other, code.Id

[<Fact>]
let ``quantified measure aliases forward the exact recalled code and environment without erasing units`` () =
    let graph, declaration, metre, second, _ = measuredFixture ()
    let ctx = context graph declaration
    let sourceShape = Operands.project ctx declaration |> ok
    Operands.bind ctx declaration (code sourceShape (Arg 0)) (Some(environment sourceShape (Arg 1))) |> ok
    for destination in [metre; second] do
        let value = Operands.reproject ctx declaration destination |> ok
        Assert.Equal(Arg 0, (Operands.code value).SSA)
        Assert.Equal(Arg 1, (heldEnvironment value).SSA)
        Assert.Equal(graph.Nodes[destination].Type, (Operands.carrier value).SourceType)
    Assert.NotEqual(graph.Nodes[metre].Type, graph.Nodes[second].Type)
    Operands.copy ctx declaration metre |> ok
    Operands.reproject ctx metre second |> failure |> ignore

[<Fact>]
let ``unquantified dimensions cannot borrow the shared signature permission`` () =
    let graph, declaration, metre, second, implementation = measuredFixture ()
    // For a code that declares no scheme the compiler service derives an empty
    // signature permission, and it settles no carrier at either alias.
    let changed =
        graph |> withoutCarrier metre |> withoutCarrier second
        |> withCallable (fun callable -> { callable with SignatureData = callable.SignatureData.Add(implementation, Set.empty) })
    Operands.project (context changed declaration) declaration |> failure |> ignore
    let carrier = graph.Codata.CallableCarriers[declaration]
    Operands.components (context graph declaration) (List.last carrier.ParameterShapes) |> failure |> ignore

let private measuredCallFixture () =
    let graph, _, occurrence, _, implementation = measuredFixture ()
    let code = graph.Nodes[implementation]
    let parameters, _ = match code.Kind with SemanticKind.Lambda(parameters, body, _, _, _) -> parameters, body | _ -> failwith "Missing code"
    let valueType = match graph.Nodes[occurrence].Type with TypeIdentity.Function(input, _) -> input | _ -> failwith "Missing public signature"
    let binding = node 18 (SemanticKind.Binding("physical", false, false, None)) code.Type [4] None
    let callee = node 19 (SemanticKind.VarRef("physical", Some binding.Id)) code.Type [] None
    let environment = node 20 (SemanticKind.EnvironmentReference occurrence) (List.head parameters |> fun (_, ty, _) -> ty) [7] None
    let argument = node 21 (SemanticKind.Literal(NativeLiteral.Float(3.0, NTUKind.NTUfloat(NTUWidth.Fixed 64)))) valueType [] None
    let call = node 22 (SemanticKind.Application(callee.Id, [environment.Id; argument.Id])) valueType [19; 20; 21] None
    let nodes = [binding; callee; environment; argument; call] |> List.fold (fun nodes node -> Map.add node.Id node nodes) graph.Nodes
    let row: Hyperedge =
        { Sources = [occurrence; implementation; environment.Id; argument.Id]; Target = call.Id
          Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentInvocation; Ordinal = 0 }
    let formals = parameters |> List.map (fun (_, _, formal) -> formal)
    let instance: CallableEmissionCall =
        { Site = call.Id; Implementation = implementation; Parameters = parameters
          Arguments = [environment.Id; argument.Id]; Result = NodeId 3
          SignatureData = Set.ofList (NodeId 3 :: formals)
          Participants = Set.ofList (ids [0; 1; 3; 4; 5; 7; 13; 19; 20; 21; 22]) }
    let declared =
        { graph.Emission.Callable.Declarations[implementation] with
            Lookup = binding.Id; Name = CallableSymbolName.RootBinding "physical"
            Participants = Set.ofList (ids [0; 1; 3; 4; 18]) }
    let called =
        { graph with Nodes = nodes; Edges = row :: graph.Edges }
        |> withCallable (fun callable ->
            { callable with
                ValueShapes = adding (callableShapes [18; 19] @ dataShapes [20; 21; 22]) callable.ValueShapes
                Calls = Map.ofList [call.Id, instance]
                Declarations = callable.Declarations.Add(binding.Id, declared)
                ClosedData = Set.union callable.ClosedData (Set.ofList (ids [20; 21; 22])) })
        |> withNumeric (fun numeric ->
            { numeric with
                OccurrenceRepresentations =
                    adding (represented byteArray [20] @ represented real [21; 22]) numeric.OccurrenceRepresentations })
        |> declareTraversalReadings
    called, call.Id, implementation, parameters, row

[<Fact>]
let ``direct physical parameters require the current instantiated call and retain symbolic shared code`` () =
    let graph, site, implementation, parameters, _ = measuredCallFixture ()
    let projected = Operands.parametersAtCall (context graph site) site implementation parameters |> ok
    Assert.Equal(2, projected.Length)
    Assert.Equal<MLIRType list>([TFloat F64], List.last projected)
    // The contract holds a free measure variable in the dimension of the type identity.
    match List.last parameters with
    | _, TypeIdentity.Numeric(_, dimension), _ -> Assert.NotEmpty dimension.Vars
    | _, other, _ -> failwithf "The shared code formal is not a measured number: %A" other
    // The shared implementation also occurs under the measured declaration.
    // Select the explicit physical binding occurrence for this refusal control;
    // a unique-occurrence observer must not choose one of those paths for us.
    let implementationPath =
        graph.SourceReadings.Contexts[implementation]
        |> List.find (fun path -> path.Head.Parent = NodeId 18)
    let outsideCall =
        { context graph site with
            Zipper = Zipper.createAt graph implementation implementationPath |> require "Missing physical implementation occurrence" }
    let reason = Operands.parametersAtCall outsideCall site implementation parameters |> failure
    Assert.Contains("requires its current Huet occurrence", reason)
    Assert.Empty outsideCall.Accumulator.AllOps
    Assert.Empty outsideCall.Accumulator.NodeAssoc
    Assert.Empty outsideCall.Accumulator.CallableAssoc

[<Theory>]
[<InlineData("missing source call")>]
[<InlineData("wrong source callable")>]
[<InlineData("changed argument dimension")>]
let ``direct parameter projection refuses broken instance correspondence`` change =
    let graph, site, implementation, parameters, row = measuredCallFixture ()
    let graph =
        match change with
        | "missing source call" -> { graph with Edges = List.tail graph.Edges }
        | "wrong source callable" -> { graph with Edges = { row with Sources = implementation :: List.tail row.Sources } :: List.tail graph.Edges }
        | "changed argument dimension" ->
            let argument = graph.Nodes[List.last row.Sources]
            { graph with Nodes = graph.Nodes.Add(argument.Id, { argument with Type = floatType }) }
        | _ -> failwith "Unknown mutation"
    // The compiler service settles no call instance at the site for any of these changes.
    let graph = graph |> withCallable (fun callable -> { callable with Calls = callable.Calls.Remove site })
    Operands.parametersAtCall (context graph site) site implementation parameters |> failure |> ignore
