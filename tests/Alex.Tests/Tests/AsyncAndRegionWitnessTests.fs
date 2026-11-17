module Alex.Tests.AsyncAndRegionWitnessTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Tests.Build
module Operands = Alex.Traversal.CallableOperands
module Zipper = Alex.Traversal.PSGZipper

// The rows below were printed from the compiler service (clef 6f1d1e2, contract
// schema 56) and copied here. The async rows are those of `asyncWithCapture` and
// of `Async.RunSynchronously (asyncWithCapture 21)` in sample 17_BasicAsync. The
// region rows are those of `processAndExtract` in sample 22_RegionEscape. Each
// fixture states the occurrences and rows the witness under test reads. A child
// occurrence the witness does not read is named in its parent and not stated; the
// fixture's positional account marks it as omitted.

let private ok = function Result.Ok value -> value | Result.Error reason -> failwith reason
let private ids numbers = List.map NodeId numbers
let private registerInt = NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register)

let private constructorOf name parameters kind : ConstructorIdentity =
    { Declaration = { Module = []; Name = name }; Parameters = parameters; NativeKind = kind }

let private asyncOf result = TypeIdentity.Application(constructorOf "Async" [ TypeParamKind.Type ] (Some NTUKind.NTUptr), [ result ])
let private storageType = TypeIdentity.Application(constructorOf "<compiler-storage>" [] None, [])
let private regionType = TypeIdentity.Application(constructorOf "Region" [] (Some NTUKind.NTUptr), [])

let private sources (numbers: int list) : Participant list =
    numbers |> List.map (fun number -> { Node = NodeId number; Role = ParticipantRole.Source; Ordinal = 0; Group = NodeId number })

let private unitLiteral number parent = node number (SemanticKind.Literal NativeLiteral.Unit) unitType [] (Some parent)

let private context (graph: Revision) (occurrence: int) : WitnessContext =
    let accumulator = MLIRAccumulator.empty ()
    let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
      ScopeContext = scope; RootScopeContext = scope; Graph = graph
      Zipper = Zipper.create graph (NodeId occurrence) |> require "Missing fixture occurrence"
      GlobalVisited = visited; TraversalVisited = visited }

let private refusal (output: WitnessOutput) =
    match output.Result with
    | TRError diagnostic -> diagnostic.Message
    | _ -> failwith "Expected a refusal"

// ═══════════════════════════════════════════════════════════════════════════
// A-01 (Alex#6): formation and activation, sample 17_BasicAsync
// ═══════════════════════════════════════════════════════════════════════════

let private octet = ValueRepresentation.Scalar(SettledSlot.Integer(8, Some "octet"))
let private environmentBytes = ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
let private deferredType = functionFrom unitType intType
let private deferredParameters = [ "__closure_environment", storageType, NodeId 193; "_async_unit", unitType, NodeId 136 ]

/// One published carrier of deferred callable 194 with its environment convention.
let private carrier occurrence formation environmentValue sourceType omitted : CallableCarrier =
    { Occurrence = NodeId occurrence; Kind = CallableKind.OrdinaryFlatClosure; Formation = NodeId formation
      EnvironmentValue = Some(NodeId environmentValue); Contract = Ok(NodeId 260); Lifetime = []
      SourceType = sourceType; Implementation = NodeId 194
      Parameters = deferredParameters
      ParameterShapes = [ CallableValueShape.Data(NodeId 193); CallableValueShape.Data(NodeId 136) ]
      OmittedParameters = omitted
      Result = NodeId 227; ResultShape = CallableValueShape.Data(NodeId 227)
      Environment = Some { Owner = NodeId 137; Formal = NodeId 193 } }

/// The formation of `asyncWithCapture` (129), its deferred closure value (137) and the
/// activation `Async.RunSynchronously (asyncWithCapture 21)` (161) with its operand (160).
/// `omitted` is the set of formals of deferred callable 194 published as omitted. The
/// compiler service publishes the empty set.
let private asyncRevision (omitted: Set<NodeId>) : Revision =
    let nodes =
        [ node 128 (SemanticKind.PatternBinding "x") intType [] None
          node 136 (SemanticKind.PatternBinding "_async_unit") unitType [] (Some 194)
          node 193 (SemanticKind.PatternBinding "__closure_environment") storageType [] (Some 194)
          node 227 (SemanticKind.Sequential(ids [ 219; 223; 226; 135 ])) intType [ 219; 223; 226; 135 ] (Some 194)
          node 194 (SemanticKind.Lambda(deferredParameters, NodeId 227, [], None, LambdaContext.RegularClosure))
               (functionFrom storageType deferredType) [ 193; 136; 227 ] (Some 195)
          node 196 (SemanticKind.EnvironmentCreate(NodeId 137, [ NodeId 128, NodeId 128 ])) storageType [] (Some 137)
          node 137 (SemanticKind.ClosureValue(NodeId 194, NodeId 196)) deferredType [ 194; 196 ] (Some 129)
          unitLiteral 138 129; unitLiteral 139 129; unitLiteral 140 129; unitLiteral 141 129
          node 142 (SemanticKind.Literal(NativeLiteral.Int(-1L, registerInt))) intType [] (Some 129)
          unitLiteral 143 129
          node 129 (SemanticKind.Sequential(ids [ 138; 139; 140; 141; 142; 143; 137 ])) (asyncOf intType)
               [ 138; 139; 140; 141; 142; 143; 137 ] (Some 144)
          unitLiteral 154 157; unitLiteral 155 157; unitLiteral 156 157
          node 157 (SemanticKind.Intrinsic { Module = IntrinsicModule.Lazy; Operation = "RunSynchronously"
                                             Category = IntrinsicCategory.Pure; FullName = "Async.RunSynchronously" })
               (functionFrom (asyncOf intType) intType) [ 154; 155; 156 ] (Some 161)
          node 160 (SemanticKind.Sequential(ids [ 206; 208 ])) (asyncOf intType) [ 206; 208 ] (Some 161)
          node 161 (SemanticKind.Application(NodeId 157, [ NodeId 160 ])) intType [ 157; 160 ] (Some 162) ]
    let declaration : CallableEmissionDeclaration =
        { Lookup = NodeId 194; Implementation = NodeId 194; Parameters = deferredParameters; Result = NodeId 227
          Context = LambdaContext.RegularClosure; Captures = []
          Name = CallableSymbolName.ModuleBinding("BasicAsyncSample", "__closure_environment_impl_137")
          Parent = Some(NodeId 195); Participants = Set.ofList (ids [ 136; 193; 194; 195; 227 ]) }
    let data = [ 128; 136; 193; 227; 196; 161; 138; 139; 140; 141; 142; 143; 154; 155; 156 ]
    let callable =
        { Empty.callable with
            Carriers =
                [ NodeId 129, carrier 129 129 129 (asyncOf intType) omitted
                  NodeId 137, carrier 137 137 196 deferredType omitted
                  NodeId 160, carrier 160 208 208 (asyncOf intType) omitted ] |> Map.ofList
            ValueShapes =
                (ids data |> List.map (fun id -> id, CallableValueShape.Data id))
                @ (ids [ 129; 137; 160; 194; 157 ] |> List.map (fun id -> id, CallableValueShape.Callable id)) |> Map.ofList
            AliasTargets = Map.ofList [ NodeId 161, NodeId 161 ]
            Transports =
                [ NodeId 129, Set.ofList (ids [ 129; 137 ])
                  NodeId 137, Set.ofList (ids [ 137 ])
                  NodeId 160, Set.ofList (ids [ 160; 208 ]) ] |> Map.ofList
            Declarations = Map.ofList [ NodeId 194, declaration ]
            SignatureData = Map.ofList [ NodeId 194, Set.empty ]
            ClosedData = Set.ofList (ids [ 128; 136; 193; 227; 196; 161 ]) }
    let numeric =
        { Empty.numeric with
            OccurrenceRepresentations =
                [ NodeId 128, Ok octet
                  NodeId 136, Ok(ValueRepresentation.Scalar SettledSlot.Unit)
                  NodeId 193, Ok environmentBytes
                  NodeId 227, Ok octet
                  NodeId 196, Ok environmentBytes
                  NodeId 160, Ok environmentBytes
                  NodeId 161, Ok octet ] |> Map.ofList }
    let slot : ContinuationSlot =
        { Source = NodeId 128; ValueType = intType; IsCapture = true
          Holds = CaptureSlotKind.Scalar(SettledSlot.Integer(8, Some "octet"))
          Field = { Name = "Capture_128"; Slot = SettledSlot.Integer(8, Some "octet"); Offset = Some 0; Size = Some 1; Align = Some 1 } }
    let layout : EnvironmentLayout =
        { Owner = NodeId 137; Implementation = NodeId 194; Formal = NodeId 193
          Slots = [ slot ]; Bytes = 1; Alignment = 1; Obligations = [ NodeId 209 ] }
    let known : KnownCallable = { Implementation = NodeId 194; EnvironmentOwner = NodeId 137 }
    let formation : AsyncFormation =
        { Formation = NodeId 129; Callable = NodeId 194; Body = NodeId 135; CapturedBindings = [ NodeId 128 ]
          ResultType = intType; ResultStorage = NodeId 138; Frame = NodeId 141; LifetimeScope = NodeId 139
          CompletionProtocol = NodeId 140; Obligations = [ NodeId 229 ]
          Participants = sources [ 129; 194; 135; 141; 138; 139; 140; 128 ] }
    let activation : AsyncActivation =
        { Site = NodeId 161; Formation = NodeId 129; ResultTarget = NodeId 154; CompletionTarget = NodeId 156
          Obligations = [ NodeId 231 ]; Participants = sources [ 161; 129; 154; 156 ] }
    let ordinary =
        if omitted.IsEmpty then Empty.emission.Ordinary
        else { Empty.emission.Ordinary with Parameters = Map.ofList [ NodeId 194, omitted ] }
    { revision nodes with
        Codata =
            { Codata.empty with
                EnvironmentLayouts = Map.ofList [ NodeId 137, layout ]
                EnvironmentOrigins = ids [ 129; 137; 160 ] |> List.map (fun id -> id, NodeId 137) |> Map.ofList
                KnownCallables = ids [ 129; 137; 160 ] |> List.map (fun id -> id, known) |> Map.ofList
                AsyncFormations = Map.ofList [ NodeId 129, formation ]
                AsyncActivations = Map.ofList [ NodeId 161, activation ] }
        Emission = { Empty.emission with Callable = callable; Numeric = numeric; Ordinary = ordinary } }
    |> declareTraversalReadings

/// Bind the operands a callable occurrence was witnessed with: its code and its environment.
let private witnessed (ctx: WitnessContext) (occurrence: int) : Val * Val =
    let shape = Operands.project ctx (NodeId occurrence) |> ok
    let code : Val = { SSA = V(occurrence, 1200); Type = Operands.functionType shape }
    let environment : Val = { SSA = Arg 0; Type = Operands.environmentType shape |> require "The fixture carrier has an environment" }
    Operands.bind ctx (NodeId occurrence) code (Some environment) |> ok
    code, environment

let private asyncWitness (ctx: WitnessContext) (occurrence: int) =
    Alex.Witnesses.AsyncWitness.nanopass.Witness ctx ctx.Graph.Nodes[NodeId occurrence]

[<Fact>]
let ``A-01 (17_BasicAsync): a published formation takes the operands of its deferred callable and emits no operation`` () =
    let graph = asyncRevision Set.empty
    let ctx = context graph 129
    let code, environment = witnessed ctx 137
    let output = asyncWitness ctx 129
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Empty ctx.Accumulator.AllOps
    match output.Result with
    | TRCallable formed ->
        Assert.Equal(code, Operands.code formed)
        Assert.Equal(Some environment, Operands.environment formed)
        let published = Operands.exactCarrier formed |> require "The formation has an exact carrier"
        Assert.Equal(NodeId 129, published.Occurrence)
        Assert.Equal(NodeId 129, published.Formation)
        Assert.Equal(NodeId 194, published.Implementation)
    | _ -> failwith "The formation did not take its deferred callable's operands"

[<Fact>]
let ``A-01 (17_BasicAsync): a formation whose published rows disagree is refused with no operation and no operand`` () =
    let published = asyncRevision Set.empty
    let withFormation change =
        { published with Codata = { published.Codata with AsyncFormations = Map.ofList [ NodeId 129, change published.Codata.AsyncFormations[NodeId 129] ] } }
    let withTransports rows =
        { published with Emission = { published.Emission with Callable = { published.Emission.Callable with Transports = rows } } }
    let cases =
        [ withFormation (fun row -> { row with Callable = NodeId 191 }), true,
          "Async formation 129: its published deferred callable 191 is not the implementation of the formation carrier and of occurrence 137."
          withTransports (published.Emission.Callable.Transports.Add(NodeId 129, Set.singleton (NodeId 129))), true,
          "Async formation 129: Emission.Callable.Transports does not name its deferred callable occurrence 137 as a source."
          withTransports (published.Emission.Callable.Transports.Remove(NodeId 129)), true,
          "Async formation 129 has no published callable transport row (Emission.Callable.Transports)."
          published, false,
          "Async formation 129: callable occurrence 137 has no witnessed callable operands in this operation scope." ]
    for graph, deferredWitnessed, expected in cases do
        let ctx = context graph 129
        if deferredWitnessed then witnessed ctx 137 |> ignore
        let output = asyncWitness ctx 129
        Assert.Equal(expected, refusal output)
        Assert.Empty output.InlineOps
        Assert.Empty output.TopLevelOps
        Assert.Empty ctx.Accumulator.AllOps
        Assert.True((MLIRAccumulator.recallCallable (NodeId 129) ctx.Accumulator).IsNone)

[<Fact>]
let ``A-01 (17_BasicAsync): the published activation names no argument for the deferred callable's unit formal and is refused`` () =
    let graph = asyncRevision Set.empty
    let ctx = context graph 161
    witnessed ctx 160 |> ignore
    let output = asyncWitness ctx 161
    Assert.Equal(
        "Async activation 161: Codata.AsyncActivations publishes no argument occurrence for formal 136 (_async_unit) of deferred callable 194, and Emission.Ordinary.Parameters does not publish that formal as omitted.",
        refusal output)
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Empty ctx.Accumulator.AllOps
    Assert.True((MLIRAccumulator.recallNode (NodeId 161) ctx.Accumulator).IsNone)

[<Fact>]
let ``A-01: an activation whose deferred callable has every formal published is one indirect call of the operand`` () =
    // The compiler service does not publish this revision: at clef 6f1d1e2 formal 136 is a
    // physical parameter of deferred callable 194 (the preceding test). This fixture states
    // the rows the Pattern reads when that formal is published as omitted, in the form
    // Emission.Ordinary.Parameters already has for an omitted formal of an ordinary callable.
    let graph = asyncRevision (Set.singleton (NodeId 136))
    let ctx = context graph 161
    let code, environment = witnessed ctx 160
    let output = asyncWitness ctx 161
    let byte = TInt(IntWidth 8)
    Assert.Equal<MLIRType>(TFunc([ TMemRefStatic(1, byte) ], [ byte ]), code.Type)
    match output.InlineOps, output.Result with
    | [ MLIROp.FuncOp(FuncOp.FuncCallIndirect([ result ], callee, arguments)) ], TRValue value ->
        Assert.Equal(code.SSA, callee)
        Assert.Equal<Val list>([ environment ], arguments)
        Assert.Equal<Val>({ SSA = V(161, 511); Type = byte }, result)
        Assert.Equal<Val>(result, value)
    | _ -> failwith "The activation is not one indirect call of its operand"
    Assert.Empty output.TopLevelOps

[<Fact>]
let ``A-01: an activation of an operand that carries another implementation is refused`` () =
    let published = asyncRevision (Set.singleton (NodeId 136))
    let formation = { published.Codata.AsyncFormations[NodeId 129] with Callable = NodeId 191 }
    let graph = { published with Codata = { published.Codata with AsyncFormations = Map.ofList [ NodeId 129, formation ] } }
    let ctx = context graph 161
    witnessed ctx 160 |> ignore
    let output = asyncWitness ctx 161
    Assert.Equal(
        "Async activation 161: operand 160 carries implementation 194, and the published formation 129 names deferred callable 191.",
        refusal output)
    Assert.Empty output.InlineOps
    Assert.Empty ctx.Accumulator.AllOps
    Assert.True((MLIRAccumulator.recallNode (NodeId 161) ctx.Accumulator).IsNone)

// ═══════════════════════════════════════════════════════════════════════════
// A-04 and A-06 (Alex#9, Alex#10): region occurrences, sample 22_RegionEscape
// ═══════════════════════════════════════════════════════════════════════════

/// `processAndExtract`: region creation (123), allocation (137), copyOut (179) and the
/// constructed scope-exit release (186). The revision holds no Emission.Memory row and
/// no Codata.Escapes row for 123, 137 or 186; Codata.Escapes holds 179.
let private regionRevision : Revision =
    let arrayType = arrayOf intType
    let nodes =
        [ unitLiteral 118 121; unitLiteral 119 121; unitLiteral 120 121
          node 121 (SemanticKind.Intrinsic { Module = IntrinsicModule.Arena; Operation = "create"
                                             Category = IntrinsicCategory.Memory; FullName = "Region.create" })
               (functionFrom intType regionType) [ 118; 119; 120 ] (Some 123)
          node 122 (SemanticKind.Literal(NativeLiteral.Int(4L, registerInt))) intType [] (Some 123)
          node 123 (SemanticKind.Application(NodeId 121, [ NodeId 122 ])) regionType [ 121; 122 ] (Some 124)
          node 137 (SemanticKind.Application(NodeId 133, ids [ 134; 136 ])) arrayType [ 133; 134; 136 ] (Some 138)
          node 179 (SemanticKind.Application(NodeId 175, ids [ 176; 178 ])) arrayType [ 175; 176; 178 ] (Some 180)
          node 186 (SemanticKind.Application(NodeId 184, [ NodeId 185 ])) unitType [ 184; 185 ] (Some 187)
          // An application the region rows do not name.
          node 300 (SemanticKind.Application(NodeId 301, [ NodeId 302 ])) intType [ 301; 302 ] None ]
    let region : RegionAllocation =
        { Region = NodeId 123; SpacePlacement = NodeId 118; ByteExtent = 24L; Capacity = 16384L; Alignment = 8
          LifetimeScope = NodeId 124; LifetimeDepth = 2; AllocatedValues = ids [ 137; 138 ]
          ScopeExitPaths = [ NodeId 187 ]; ScopeExitReleases = [ NodeId 187, NodeId 186 ]
          Obligations = [ NodeId 431 ]; Participants = sources [ 123; 118; 124; 137; 138; 187; 186 ] }
    let copy : RegionCopyEndpoint =
        { Site = NodeId 179; Kind = RegionCopyKind.CopyOut; EscapingValue = NodeId 137; SourceRegion = NodeId 123
          SourceView = NodeId 176; SourceByteExtent = 24L; SourceCapacity = 16384L; SourceAlignment = 8
          SourceLifetimeScope = NodeId 124; SourceLifetimeDepth = 2
          DestinationRegion = None; DestinationStorage = NodeId 179; DestinationByteExtent = 24L
          DestinationCapacity = 24L; DestinationAlignment = 8
          DestinationLifetimeScope = NodeId 194; DestinationLifetimeDepth = 1
          EscapeDischargeObligation = NodeId 434; Participants = sources [ 179; 137; 123; 176; 124; 194 ] }
    { revision nodes with
        Codata =
            { Codata.empty with
                Escapes = Map.ofList [ NodeId 179, EscapeKind.EscapesViaReturn ]
                RegionAllocations = Map.ofList [ NodeId 123, region ]
                RegionCopyEndpoints = Map.ofList [ NodeId 179, copy ] } }
    |> declareTraversalReadings

let private regionCases =
    [ 123, "Region creation 123: Codata.RegionAllocations publishes a capacity of 16384 bytes at alignment 8, and the revision publishes no storage operation for the region (no Emission.Memory.Operations row at node 123). Alex does not choose a residence or placement for region storage."
      137, "Region allocation 137 in region 123: the revision publishes no byte offset for this value within the region's 24-byte extent (no Emission.Memory.Operations row at node 137). Alex does not compute allocation offsets."
      179, "Region copy endpoint 179 (copyOut): Codata.RegionCopyEndpoints publishes a 24-byte source extent and destination storage 179, and the revision publishes no copy operation for it (no Emission.Memory.ArrayCopies or Emission.Memory.Operations row at node 179). Alex does not choose the destination allocation."
      186, "Region release 186 of region 123: the revision publishes no storage operation for the region it releases (no Emission.Memory.Operations row at node 186)." ]

[<Fact>]
let ``A-04 and A-06 (22_RegionEscape): region occurrences with no published storage operation are refused by their rows`` () =
    for occurrence, expected in regionCases do
        let ctx = context regionRevision occurrence
        let output = Alex.Witnesses.RegionWitness.nanopass.Witness ctx regionRevision.Nodes[NodeId occurrence]
        Assert.Equal(expected, refusal output)
        Assert.Empty output.InlineOps
        Assert.Empty output.TopLevelOps
        Assert.Empty ctx.Accumulator.AllOps
        Assert.True((MLIRAccumulator.recallNode (NodeId occurrence) ctx.Accumulator).IsNone)

[<Fact>]
let ``A-04: the region witness leaves an application the region rows do not name to the other witnesses`` () =
    let ctx = context regionRevision 300
    let output = Alex.Witnesses.RegionWitness.nanopass.Witness ctx regionRevision.Nodes[NodeId 300]
    Assert.Equal(TRSkip, output.Result)

[<Fact>]
let ``A-04 (22_RegionEscape): the CPU registry refuses region creation and allocation by their rows and emits no storage for them`` () =
    // Before the region witness, the intrinsic dispatch of `Region.create 4` read the literal
    // operand as a byte count and emitted a 4-byte stack allocation, and `Region.alloc`
    // reported an arena residence. Both occurrences are now refused by their published rows.
    let registry = Alex.Traversal.WitnessRegistry.createRegistry Alex.Target.CPU
    let witness = combineWitnesses registry.Nanopasses
    for occurrence, expected in regionCases do
        let ctx = context regionRevision occurrence
        let output = witness ctx regionRevision.Nodes[NodeId occurrence]
        Assert.Equal(expected, refusal output)
        Assert.Empty output.InlineOps
        Assert.Empty output.TopLevelOps
        Assert.Empty ctx.Accumulator.AllOps
        Assert.True((MLIRAccumulator.recallNode (NodeId occurrence) ctx.Accumulator).IsNone)
