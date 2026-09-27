module Alex.Tests.CallableTransportTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
module Operands = Alex.Traversal.CallableOperands
module Zipper = Alex.Traversal.PSGZipper

let private ok = function Result.Ok value -> value | Result.Error reason -> failwith reason

let private regular = LambdaContext.RegularClosure
let private ids numbers = List.map NodeId numbers
let private dataShapes numbers = ids numbers |> List.map (fun id -> id, CallableValueShape.Data id)
let private callableShapes numbers = ids numbers |> List.map (fun id -> id, CallableValueShape.Callable id)
let private represented form numbers = ids numbers |> List.map (fun id -> id, Ok form)
let private transports rows = rows |> List.map (fun (destination, sources) -> NodeId destination, Set.ofList (ids sources))
let private adding rows table = rows |> List.fold (fun held (key, value) -> Map.add key value held) table

let private flag = ValueRepresentation.Scalar SettledSlot.Bool
/// The published form of the one byte environment at its formal.
let private environmentBytes = ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
/// The published form of a byte array that has no settled extent.
let private byteArray = ValueRepresentation.Buffer(None, ValueRepresentation.Scalar(SettledSlot.Integer(8, Some "uint8")))

let private withCodata change (graph: Revision) = { graph with Codata = change graph.Codata }
let private withCallable change (graph: Revision) =
    { graph with Emission = { graph.Emission with Callable = change graph.Emission.Callable } }

let private ty = functionFrom boolType boolType
let private envTy = arrayOf uint8Type

/// These fixtures establish passive physical transport, not source lifetime proof.
/// The carriers are the ones the source-owned carrier projector settles, and the
/// rows are the ones the compiler service publishes for these participants.
let private fixture captured =
    let parameters = (if captured then ["environment", envTy, NodeId 0] else []) @ ["value", boolType, NodeId 1]
    let physical = if captured then functionFrom envTy ty else ty
    let owner = if captured then 6 else 4
    let nodes =
        [ node 0 (SemanticKind.PatternBinding "environment") envTy [] None
          node 1 (SemanticKind.PatternBinding "value") boolType [] None
          node 2 (SemanticKind.VarRef("value", Some(NodeId 1))) boolType [] None
          node 3 (SemanticKind.Lambda(parameters, NodeId 2, [], None, regular)) physical (if captured then [0; 1; 2] else [1; 2]) (Some 4)
          node 4 (SemanticKind.Binding("code", false, false, None)) physical [3] None
          node 5 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
          (if captured then node 6 (SemanticKind.ClosureValue(NodeId 3, NodeId 7)) ty [3; 7] None
           else node 6 (SemanticKind.PatternBinding "closure") ty [] None)
          node 7 (SemanticKind.EnvironmentCreate(NodeId 6, [NodeId 5, NodeId 5])) envTy [] None
          node 8 (SemanticKind.Binding("alias", false, false, None)) ty [owner] (Some 12)
          node 9 (SemanticKind.VarRef("alias", Some(NodeId 8))) ty [] (Some 10)
          node 10 (SemanticKind.TypeAnnotation(NodeId 9, ty)) ty [9] (Some 12)
          node 11 (SemanticKind.VarRef("code", Some(NodeId 4))) physical [] (Some 12)
          node 12 (SemanticKind.Sequential [NodeId 8; NodeId 11; NodeId 10]) ty [8; 11; 10] None ]
    let carrier occurrence : CallableCarrier =
        { Occurrence = NodeId occurrence; SourceType = ty; Implementation = NodeId 3
          Parameters = parameters
          ParameterShapes = parameters |> List.map (fun (_, _, formal) -> CallableValueShape.Data formal)
          OmittedParameters = Set.empty
          Result = NodeId 2; ResultShape = CallableValueShape.Data(NodeId 2)
          Environment = if captured then Some { Owner = NodeId 6; Formal = NodeId 0 } else None }
    let occurrences = if captured then [6; 8; 9; 10; 12] else [3; 4; 8; 9; 10; 11; 12]
    let carriers = occurrences |> List.map (fun occurrence -> NodeId occurrence, carrier occurrence) |> Map.ofList
    let slot: ContinuationSlot =
        { Source = NodeId 5; ValueType = boolType; Holds = CaptureSlotKind.Scalar SettledSlot.Bool; IsCapture = true
          Field = { Name = "capture"; Slot = SettledSlot.Bool; Offset = Some 0; Size = Some 1; Align = Some 1 } }
    let layout: EnvironmentLayout =
        { Owner = NodeId 6; Implementation = NodeId 3; Formal = NodeId 0; Slots = [slot]; Bytes = 1; Alignment = 1; Obligations = [] }
    let edges: Hyperedge list =
        if captured then
            [{ Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentFormal; Sources = [NodeId 6; NodeId 3]; Target = NodeId 0; Ordinal = 0 }
             { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentCapture false; Sources = [NodeId 6; NodeId 5; NodeId 5]; Target = NodeId 7; Ordinal = 0 }]
        else []
    let codata =
        if captured then
            { Codata.empty with
                CallableCarriers = carriers
                EnvironmentLayouts = Map.ofList [NodeId 6, layout]
                EnvironmentOrigins = ids (0 :: occurrences) |> List.map (fun id -> id, NodeId 6) |> Map.ofList
                KnownCallables =
                    ids occurrences |> List.map (fun id -> id, { Implementation = NodeId 3; EnvironmentOwner = NodeId 6 }) |> Map.ofList }
        else { Codata.empty with CallableCarriers = carriers }
    let declaration lookup parent : CallableEmissionDeclaration =
        { Lookup = NodeId lookup; Implementation = NodeId 3; Parameters = parameters; Result = NodeId 2
          Context = regular; Captures = []; Name = CallableSymbolName.RootBinding "code"
          Parent = Option.map NodeId parent
          Participants = Set.ofList (ids ((if captured then [0] else []) @ [1; 2; 3; 4])) }
    let callable =
        { Empty.callable with
            Carriers = carriers
            ValueShapes = dataShapes [0; 1; 2; 5; 7] @ callableShapes [3; 4; 6; 8; 9; 10; 11; 12] |> Map.ofList
            SignatureData = Map.ofList [NodeId 3, Set.empty]
            Transports =
                (if captured then
                    transports [6, [6]; 8, [6; 8]; 9, [6; 8; 9]; 10, [6; 8; 9; 10]; 12, [6; 8; 9; 10; 12]]
                 else
                    transports [3, [3]; 4, [3; 4]; 8, [3; 4; 8]; 9, [3; 4; 8; 9]; 10, [3; 4; 8; 9; 10]
                                11, [3; 4; 11]; 12, [3; 4; 8; 9; 10; 12]]) |> Map.ofList
            Declarations = Map.ofList [NodeId 3, declaration 3 (Some 4); NodeId 4, declaration 4 None]
            Symbols =
                Map.ofList [NodeId 3, CallableSymbolName.RootBinding "code"
                            NodeId 4, CallableSymbolName.RootBinding "code"
                            NodeId 8, CallableSymbolName.LocalBinding(NodeId 8, "alias")]
            DirectCallees = Map.ofList [NodeId 11, NodeId 4]
            FunctionBindings = Set.ofList [NodeId 4]
            DefinitionOnlyBindings = Set.ofList [NodeId 4]
            DefinitionOnlyLambdas = Set.ofList [NodeId 3]
            ClosedData = Set.ofList (ids [0; 1; 2; 5; 7]) }
    let numeric =
        { Empty.numeric with
            OccurrenceRepresentations =
                represented (if captured then environmentBytes else byteArray) [0]
                @ represented flag [1; 2; 5] @ represented byteArray [7] |> Map.ofList }
    let graph =
        { revision nodes with
            Edges = edges
            Codata = codata
            Emission = { Empty.emission with Callable = callable; Numeric = numeric } }
    graph, NodeId owner, NodeId 8, NodeId 9, NodeId 10, NodeId 12, NodeId 11

let private context graph position accumulator =
    let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
      ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
      GlobalVisited = visited; TraversalVisited = visited }

let private bindResult id (output: WitnessOutput) accumulator =
    match output.Result with
    | TRCallable value -> MLIRAccumulator.bindCallable id value accumulator |> ok; value
    | other -> failwithf "Expected separate callable operands: %A" other

[<Fact>]
let ``immutable binding reference annotation and sequence preserve the actual callable operands`` () =
    let graph, owner, alias, reference, annotation, sequence, _ = fixture true
    let operands = MLIRAccumulator.empty ()
    let root = Zipper.create graph sequence |> require "Missing sequence"
    let ownerContext = context graph root operands
    let shape = Operands.project ownerContext owner |> ok
    let code = { SSA = Arg 0; Type = Operands.functionType shape }
    let environment = { SSA = Arg 2; Type = Operands.environmentType shape |> require "No environment" }
    Operands.bind ownerContext owner code (Some environment) |> ok
    let witnesses =
        [alias, atChild alias root, Alex.Witnesses.BindingWitness.nanopass
         reference, atChild annotation root |> atChild reference, Alex.Witnesses.VarRefWitness.nanopass
         annotation, atChild annotation root, Alex.Witnesses.TypeAnnotationWitness.nanopass
         sequence, root, Alex.Witnesses.StructuralWitness.nanopass]
    for id, position, witness in witnesses do
        let ctx = context graph position operands
        let output = witness.Witness ctx graph.Nodes[id]
        let copied = bindResult id output operands
        Assert.Empty output.InlineOps
        Assert.Empty output.TopLevelOps
        Assert.Equal(id, (Operands.carrier copied).Occurrence)
        Assert.Equal(code, Operands.code copied)
        Assert.Equal(Some environment, Operands.environment copied)
        Assert.True((MLIRAccumulator.recallNode id operands).IsNone)
        Assert.Same(position, ctx.Zipper)
        Assert.Empty ctx.TraversalVisited.Value
    Assert.Empty operands.Errors

[<Fact>]
let ``named code value emits one typed function constant without an environment or thunk`` () =
    let graph, _, _, _, _, sequence, named = fixture false
    let root = Zipper.create graph sequence |> require "Missing sequence"
    let operands = MLIRAccumulator.empty ()
    let ctx = context graph (atChild named root) operands
    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx graph.Nodes[named]
    let value = bindResult named output operands
    Assert.Equal(None, Operands.environment value)
    Assert.Single(Operands.values value) |> ignore
    Assert.Empty output.TopLevelOps
    match Assert.Single output.InlineOps with
    | MLIROp.FuncOp(FuncOp.FuncConstant(ssa, symbol, ty)) ->
        Assert.Equal((Operands.code value).SSA, ssa)
        Assert.Equal((Operands.code value).Type, ty)
        Assert.Equal("code", symbol)
    | operation -> failwithf "Named code was not a direct function constant: %A" operation

/// A named function applied through the given number of annotations of its
/// reference. The rows are the ones the compiler service publishes for it.
let private annotatedCallee depth =
    let signature = functionFrom boolType boolType
    let reference = 4
    let annotations = [1 .. depth] |> List.map (fun ordinal -> reference + ordinal)
    let callee = annotations |> List.tryLast |> Option.defaultValue reference
    let argument, application, root = reference + depth + 1, reference + depth + 2, reference + depth + 3
    let wrapped = List.zip annotations (reference :: annotations |> List.take depth)
    let holder occurrence = annotations |> List.tryFind (fun annotation -> annotation = occurrence + 1) |> Option.defaultValue application
    let parameters = ["value", boolType, NodeId 0]
    let nodes =
        [ node 0 (SemanticKind.PatternBinding "value") boolType [] (Some 2)
          node 1 (SemanticKind.VarRef("value", Some(NodeId 0))) boolType [] (Some 2)
          node 2 (SemanticKind.Lambda(parameters, NodeId 1, [], None, regular)) signature [0; 1] (Some 3)
          node 3 (SemanticKind.Binding("identity", false, false, None)) signature [2] (Some root)
          node reference (SemanticKind.VarRef("identity", Some(NodeId 3))) signature [] (Some(holder reference)) ]
        @ (wrapped |> List.map (fun (annotation, inner) ->
            node annotation (SemanticKind.TypeAnnotation(NodeId inner, signature)) signature [inner] (Some(holder annotation))))
        @ [ node argument (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] (Some application)
            node application (SemanticKind.Application(NodeId callee, [NodeId argument])) boolType [callee; argument] (Some root)
            node root (SemanticKind.Sequential [NodeId 3; NodeId application]) boolType [3; application] None ]
    let occurrences = [2; 3; reference] @ annotations
    let carrier occurrence : CallableCarrier =
        { Occurrence = NodeId occurrence; SourceType = signature; Implementation = NodeId 2
          Parameters = parameters; ParameterShapes = [CallableValueShape.Data(NodeId 0)]
          OmittedParameters = Set.empty
          Result = NodeId 1; ResultShape = CallableValueShape.Data(NodeId 1)
          Environment = None }
    let carriers = occurrences |> List.map (fun occurrence -> NodeId occurrence, carrier occurrence) |> Map.ofList
    let declaration lookup parent : CallableEmissionDeclaration =
        { Lookup = NodeId lookup; Implementation = NodeId 2; Parameters = parameters; Result = NodeId 1
          Context = regular; Captures = []; Name = CallableSymbolName.LocalBinding(NodeId 3, "identity")
          Parent = Some(NodeId parent); Participants = Set.ofList (ids [0; 1; 2; 3]) }
    let call: CallableEmissionCall =
        { Site = NodeId application; Implementation = NodeId 2; Parameters = parameters
          Arguments = [NodeId argument]; Result = NodeId 1; SignatureData = Set.empty
          Participants = Set.ofList (ids [0; 1; 2; callee; argument; application]) }
    let data = [0; 1; argument; application; root]
    let callable =
        { Empty.callable with
            Carriers = carriers
            ValueShapes = dataShapes data @ callableShapes occurrences |> Map.ofList
            SignatureData = Map.ofList [NodeId 2, Set.empty]
            Calls = Map.ofList [NodeId application, call]
            Transports =
                occurrences |> List.mapi (fun position occurrence -> occurrence, List.take (position + 1) occurrences)
                |> transports |> Map.ofList
            Declarations = Map.ofList [NodeId 2, declaration 2 3; NodeId 3, declaration 3 root]
            Symbols = ids [2; 3] |> List.map (fun id -> id, CallableSymbolName.LocalBinding(NodeId 3, "identity")) |> Map.ofList
            DirectCallees = ids (reference :: annotations) |> List.map (fun id -> id, NodeId 3) |> Map.ofList
            FunctionBindings = Set.ofList [NodeId 3]
            DefinitionOnlyBindings = Set.ofList [NodeId 3]
            DefinitionOnlyLambdas = Set.ofList [NodeId 2]
            ClosedData = Set.ofList (ids data) }
    let numeric = { Empty.numeric with OccurrenceRepresentations = represented flag data |> Map.ofList }
    let graph =
        { revision nodes with
            Codata = { Codata.empty with CallableCarriers = carriers }
            Emission = { Empty.emission with Callable = callable; Numeric = numeric } }
    graph, NodeId reference, ids annotations, NodeId application, NodeId root

[<Theory>]
[<InlineData(0)>]
[<InlineData(1)>]
[<InlineData(2)>]
let ``named callee annotations retain the actual code operand at each wrapper occurrence`` depth =
    let graph, reference, annotations, application, root = annotatedCallee depth
    let operands = MLIRAccumulator.empty ()
    let applicationPosition = Zipper.create graph root |> require "Missing root" |> atChild application
    let mutable referencePosition = applicationPosition
    let mutable positions = Map.empty
    for annotation in List.rev annotations do
        referencePosition <- atChild annotation referencePosition
        positions <- positions.Add(annotation, referencePosition)
    referencePosition <- atChild reference referencePosition
    let ctx = context graph referencePosition operands
    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx graph.Nodes[reference]
    if depth = 0 then
        match output.Result with TRVoid -> () | other -> failwithf "Direct callee unexpectedly requires a value: %A" other
        Assert.Empty output.InlineOps
        Assert.Empty operands.CallableAssoc
    else
        let original = bindResult reference output operands
        Assert.Single(output.InlineOps) |> ignore
        Assert.Equal(None, Operands.environment original)
        for annotation in annotations do
            let ctx = context graph positions[annotation] operands
            let forwarded = Alex.Witnesses.TypeAnnotationWitness.nanopass.Witness ctx graph.Nodes[annotation]
            let actual = bindResult annotation forwarded operands
            Assert.Equal(Operands.code original, Operands.code actual)
            Assert.Equal(None, Operands.environment actual)
            Assert.Equal(annotation, (Operands.carrier actual).Occurrence)
            Assert.Empty forwarded.InlineOps
            Assert.Empty forwarded.TopLevelOps
    Assert.Empty operands.Errors

[<Fact>]
let ``passive callable copy cannot recover an environment from a scalar packed value`` () =
    let graph, owner, alias, _, _, sequence, _ = fixture true
    let root = Zipper.create graph sequence |> require "Missing sequence"
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode owner (Arg 0) (TMemRefStatic(2, TIndex)) operands
    let ctx = context graph (atChild alias root) operands
    let output = Alex.Witnesses.BindingWitness.nanopass.Witness ctx graph.Nodes[alias]
    match output.Result with TRError _ -> () | other -> failwithf "Scalar fallback accepted: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty operands.CallableAssoc

[<Fact>]
let ``transparent callable transport requires the destination occurrence carrier and actual Huet focus`` () =
    let graph, owner, alias, reference, annotation, sequence, _ = fixture true
    let operands = MLIRAccumulator.empty ()
    let root = Zipper.create graph sequence |> require "Missing sequence"
    let ctx = context graph (atChild alias root) operands
    let shape = Operands.project ctx owner |> ok
    Operands.bind ctx owner { SSA = Arg 0; Type = Operands.functionType shape }
        (Some { SSA = Arg 1; Type = Operands.environmentType shape |> require "No environment" }) |> ok
    let otherPosition = atChild annotation root |> atChild reference
    match matchAt (Alex.Patterns.CallablePatterns.pCallableForward ctx owner) otherPosition 64 operands with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "A reused node identity must not replace its actual occurrence"
    // The changed revision holds no carrier row of the alias, in the codata or in the callable projection.
    let changed =
        graph
        |> withCodata (fun codata -> { codata with CallableCarriers = codata.CallableCarriers.Remove alias })
        |> withCallable (fun callable -> { callable with Carriers = callable.Carriers.Remove alias })
    let position = Zipper.create changed sequence |> require "Missing sequence" |> atChild alias
    let ctx = context changed position operands
    let output = Alex.Witnesses.BindingWitness.nanopass.Witness ctx changed.Nodes[alias]
    match output.Result with TRError _ -> () | other -> failwithf "Missing destination carrier accepted: %A" other
    Assert.True((MLIRAccumulator.recallCallable alias operands).IsNone)

/// An intrinsic under the given number of annotations, applied or bound. The
/// compiler service publishes the bound fixtures. It refuses the numeric domain
/// of the applied fixtures, whose integer argument declares no range, and the
/// rows stated for them are the callable domain it derives for the same graph.
let private annotatedIntrinsic applied depth =
    let resultType = arrayOf boolType
    let functionType = functionFrom intType resultType
    let annotations = [1 .. depth]
    let outer = List.last annotations
    let aliases = 0 :: annotations
    let root = if applied then depth + 2 else depth + 1
    let wrappers =
        node 0 (SemanticKind.Intrinsic { Module = IntrinsicModule.Array; Operation = "zeroCreate"
                                         Category = IntrinsicCategory.Memory; FullName = "Array.zeroCreate" })
             functionType [] (Some 1)
        :: (annotations |> List.map (fun annotation ->
            node annotation (SemanticKind.TypeAnnotation(NodeId(annotation - 1), functionType)) functionType [annotation - 1]
                 (Some(if annotation = outer then root else annotation + 1))))
    let holders, callable =
        if applied then
            let argument = depth + 1
            [ node argument (SemanticKind.Literal(NativeLiteral.Int(2L, NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register)))) intType [] None
              node root (SemanticKind.Application(NodeId outer, [NodeId argument])) resultType [outer; argument] None ],
            { Empty.callable with
                ValueShapes = callableShapes aliases @ dataShapes [argument; root] |> Map.ofList
                IntrinsicAliases = Set.ofList (ids aliases)
                ClosedData = Set.ofList (ids [argument; root]) }
        else
            [ node root (SemanticKind.Binding("value", false, false, None)) functionType [outer] None ],
            { Empty.callable with
                ValueShapes = callableShapes (aliases @ [root]) |> Map.ofList
                Symbols = Map.ofList [NodeId root, CallableSymbolName.RootBinding "value"]
                IntrinsicAliases = Set.ofList (ids aliases) }
    { revision (wrappers @ holders) with Emission = { Empty.emission with Callable = callable } }, ids annotations, NodeId root

[<Theory>]
[<InlineData(true, 1)>]
[<InlineData(true, 2)>]
[<InlineData(false, 1)>]
[<InlineData(false, 2)>]
let ``intrinsic annotations are compile-time callees only at an actual application`` applied depth =
    let graph, annotations, root = annotatedIntrinsic applied depth
    let operands = MLIRAccumulator.empty ()
    let position = Zipper.create graph root |> require "Missing annotation fixture"
    let mutable focus = position
    for annotation in List.rev annotations do
        focus <- atChild annotation focus
        let ctx = context graph focus operands
        let output = Alex.Witnesses.TypeAnnotationWitness.nanopass.Witness ctx graph.Nodes[annotation]
        match applied, output.Result with
        | true, TRVoid | false, TRError _ -> ()
        | _ -> failwithf "Incorrect annotation role: %A" output.Result
        Assert.Empty output.InlineOps
        Assert.Empty output.TopLevelOps
    Assert.Empty operands.CallableAssoc

/// The captured fixture, with a sequence generator that reads the closure from
/// its frame. The compiler service refuses the numeric domain of this fixture,
/// whose state formal declares no range. The callable rows are the callable
/// domain it derives for the same graph. The frame and the origins are the
/// values the fixture declares.
let private continuationRead foreignOwner =
    let original, owner, _, _, _, _, _ = fixture true
    let source = original.Nodes[owner]
    let iteratorType = enumeratorOf boolType
    let frameOwner, frameFormal, frameValue, read, generator = NodeId 17, NodeId 18, NodeId 19, NodeId 20, NodeId 23
    let capture: CaptureInfo = { Name = "callback"; Type = source.Type; IsMutable = false; SourceNodeId = Some owner }
    let nodes =
        [ node 17 (SemanticKind.SeqExpr(generator, [capture])) (sequenceOf boolType) [23] None
          node 18 (SemanticKind.PatternBinding "frame") iteratorType [] None
          node 19 (SemanticKind.VarRef("frame", Some frameFormal)) iteratorType [] None
          node 20 (SemanticKind.FrameRead(frameValue, owner)) source.Type [19] None
          node 21 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
          node 22 (SemanticKind.Sequential [read; NodeId 21]) boolType [20; 21] None
          node 23 (SemanticKind.Lambda(["frame", iteratorType, frameFormal], NodeId 22, [], None, LambdaContext.SeqGenerator))
               (functionFrom iteratorType boolType) [18; 22] None
          node 24 (SemanticKind.PatternBinding "state") intType [] None
          node 25 (SemanticKind.PatternBinding "current") boolType [] None ]
    let slot: ContinuationSlot =
        { Source = owner; ValueType = source.Type; IsCapture = true
          Holds = CaptureSlotKind.EnvironmentView(if foreignOwner then frameValue else owner)
          Field = { Name = "callback"; Slot = SettledSlot.Pointer 5; Offset = Some 0; Size = Some 40; Align = Some 8 } }
    let frame: ContinuationFrame =
        { Owner = frameOwner; Generator = generator; Formal = frameFormal
          State = NodeId 24; Current = NodeId 25; Slots = [slot]; Bytes = 40; Alignment = 8
          ScratchSlots = []; ScratchBytes = 0; ScratchAlignment = 1; Initializers = [owner, owner]
          ResumeStates = []; Obligations = [] }
    let access: Hyperedge list =
        [{ Sources = [owner]; Target = read; Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationValue; Ordinal = 0 }
         { Sources = [frameOwner; generator; frameFormal; owner]; Target = read
           Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationSlotAccess; Ordinal = 0 }]
    let carrier = { original.Codata.CallableCarriers[owner] with Occurrence = read }
    let declared: CallableEmissionDeclaration =
        { Lookup = generator; Implementation = generator
          Parameters = ["frame", iteratorType, frameFormal]; Result = NodeId 22
          Context = LambdaContext.SeqGenerator; Captures = []
          Name = CallableSymbolName.Anonymous generator; Parent = None
          Participants = Set.ofList [frameFormal; NodeId 22; generator] }
    let graph =
        { original with
            Nodes = nodes |> List.fold (fun held added -> Map.add added.Id added held) original.Nodes
            Edges = original.Edges @ access }
        |> withCodata (fun codata ->
            { codata with
                CallableCarriers = codata.CallableCarriers.Add(read, carrier)
                KnownCallables = codata.KnownCallables.Add(read, codata.KnownCallables[owner])
                EnvironmentOrigins = codata.EnvironmentOrigins.Add(read, owner)
                SequenceOrigins = Map.ofList [frameValue, frameOwner; frameFormal, frameOwner]
                ContinuationFrames = Map.ofList [frameOwner, frame] })
        |> withCallable (fun callable ->
            { callable with
                Carriers = callable.Carriers.Add(read, carrier)
                ValueShapes =
                    callable.ValueShapes
                    |> adding ((frameOwner, CallableValueShape.Sequence frameOwner)
                               :: dataShapes [18; 19; 21; 22; 24; 25] @ callableShapes [20; 23])
                Transports = callable.Transports.Add(read, Set.ofList [read])
                Declarations = callable.Declarations.Add(generator, declared)
                Symbols = callable.Symbols.Add(generator, CallableSymbolName.Anonymous generator)
                ClosedData = Set.union callable.ClosedData (Set.ofList (ids [17; 18; 19; 21; 22; 24; 25])) })
    graph, frameValue, read

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``continuation callable read preserves its loaded environment and requires the exact slot owner`` foreignOwner =
    let graph, frameValue, read = continuationRead foreignOwner
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode frameValue (Arg 0) (TMemRefStatic(40, TInt(IntWidth 8))) operands
    let ctx = context graph (Zipper.create graph read |> require "Missing frame read") operands
    let output = Alex.Witnesses.SeqWitness.nanopass.Witness ctx graph.Nodes[read]
    if foreignOwner then
        match output.Result with TRError _ -> () | other -> failwithf "Foreign slot owner was accepted: %A" other
        Assert.Empty output.InlineOps
    else
        let callable = bindResult read output operands
        let environment = Operands.environment callable |> require "Loaded environment was lost"
        Assert.Equal(V(NodeId.value read, 0), environment.SSA)
        Assert.NotEqual(environment.SSA, (Operands.code callable).SSA)
        Assert.Equal(TMemRefStatic(1, TInt(IntWidth 8)), environment.Type)
        Assert.Single(output.InlineOps |> List.filter (function MLIROp.FuncOp(FuncOp.FuncConstant _) -> true | _ -> false)) |> ignore
        Assert.True((MLIRAccumulator.recallNode read operands).IsNone)
