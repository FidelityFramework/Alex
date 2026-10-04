module Alex.Tests.CallableAggregatePatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
module Operands = Alex.Traversal.CallableOperands
module Zipper = Alex.Traversal.PSGZipper

let private good = function Result.Ok value -> value | Result.Error reason -> failwith reason

let private context (graph: Revision) (occurrence: NodeId) operands : WitnessContext =
    let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = operands; RootAccumulator = operands
      ScopeContext = scope; RootScopeContext = scope; Graph = graph
      Zipper = Zipper.create graph occurrence |> require "Missing aggregate occurrence"
      GlobalVisited = visited; TraversalVisited = visited }

/// These contract fixtures state only rows read by the passive component
/// pattern. Source settlement, public-image integrity and residence discharge
/// are separate tests; no source acceptance is implied by these declarations.
let private fixture union =
    let callableType = functionFrom boolType boolType
    let aggregateType =
        if union then optionOf callableType
        else TypeIdentity.Application(
            { Declaration = { Module = ["Fixture"]; Name = "Holder" }; Parameters = []; NativeKind = None }, [])
    let formal = node 0 (SemanticKind.PatternBinding "value") boolType [] None
    let body = node 1 (SemanticKind.VarRef("value", Some formal.Id)) boolType [] None
    let implementation = node 2 (SemanticKind.Lambda(["value", boolType, formal.Id], body.Id, [], None, LambdaContext.RegularClosure)) callableType [0; 1] None
    let code = node 3 (SemanticKind.Binding("identity", false, false, None)) callableType [2] None
    let flag = node 6 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let aggregate =
        if union then node 4 (SemanticKind.DUConstruct("Some", 1, Some code.Id, None)) aggregateType [3] None
        else node 4 (SemanticKind.RecordExpr(["Work", code.Id; "Flag", flag.Id], None)) aggregateType [3; 6] None
    let read =
        if union then node 5 (SemanticKind.DUEliminate(aggregate.Id, 1, "Some", callableType)) callableType [4] None
        else node 5 (SemanticKind.FieldGet(aggregate.Id, "Work")) callableType [4] None
    let held = [formal; body; implementation; code; aggregate; read; flag]
    let carrier occurrence : CallableCarrier =
        { Occurrence = occurrence; Kind = CallableKind.OrdinaryFlatClosure; Formation = implementation.Id
          EnvironmentValue = None; Contract = Result.Ok implementation.Id; Lifetime = []
          SourceType = callableType; Implementation = implementation.Id
          Parameters = ["value", boolType, formal.Id]; ParameterShapes = [CallableValueShape.Data formal.Id]
          OmittedParameters = Set.empty; Result = body.Id; ResultShape = CallableValueShape.Data body.Id
          Environment = None }
    let carriers = [code.Id, carrier code.Id; read.Id, carrier read.Id] |> Map.ofList
    let contract : CallableContract =
        { Identity = implementation.Id; Kind = CallableKind.OrdinaryFlatClosure
          ParameterTypes = [boolType]; OmittedParameters = []
          ParameterRepresentations = [0, ValueRepresentation.Scalar SettledSlot.Bool]
          ResultType = boolType; ResultRepresentation = ValueRepresentation.Scalar SettledSlot.Bool
          EnvironmentBytes = None; Participants = [] }
    let slot : CallableAggregateSlot =
        { Identity = NodeId 99; AggregateType = aggregateType; Declaration = None; DeclarationFacts = []
          Path = [if union then CallableAggregatePathStep.UnionPayload(1, 0) else CallableAggregatePathStep.RecordField 0]
          SourceType = callableType; Contract = Result.Ok contract.Identity; Participants = [] }
    let alternative : CallableAggregateAlternative =
        { Ordinal = 0; Carrier = code.Id; Formation = implementation.Id; EnvironmentValue = None
          Contract = contract.Identity; Adapter = None; EnvironmentPlacement = None }
    let tag =
        if union then Some { Constructor = aggregate.Id; TagRead = None; CaseOrdinal = 1
                             PayloadOrdinal = Some 0; Payload = Some code.Id; Participants = [] }
        else None
    let row occurrence operation value selected : CallableAggregateValue =
        { Occurrence = occurrence; Aggregate = aggregate.Id; Slot = slot.Identity
          Alternatives = [alternative]
          Selector = Some { Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None }
          FormationInputs = [code.Id]; Value = value; SelectedAlternative = selected
          Operation = operation; Frontier = if operation = CallableAggregateOperation.Project then Some occurrence else None
          Tag = tag; Bytes = 0; Alignment = 1; Participants = [] }
    let construction = row aggregate.Id CallableAggregateOperation.Construct (Some code.Id) (Some 0)
    let projection = row read.Id CallableAggregateOperation.Project None None
    let account (value: CallableAggregateValue) : CallableAggregateDependencyAccount =
        { Occurrence = value.Occurrence; Slots = [slot]; Values = [value]; Carriers = List.ofSeq carriers.Values
          Contracts = [contract]; Flows = []; Joins = []; Participants = []; Sources = []; Claims = [] }
    let declaration : CallableEmissionDeclaration =
        { Lookup = implementation.Id; Implementation = implementation.Id
          Parameters = ["value", boolType, formal.Id]; Result = body.Id; Context = LambdaContext.RegularClosure
          Captures = []; Name = CallableSymbolName.RootBinding "identity"; Parent = None
          Participants = Set.ofList [formal.Id; body.Id; implementation.Id] }
    let data = ValueRepresentation.Record([], Some([], 0, 1))
    let componentValue = ValueRepresentation.CallableComponent(slot.Identity, data)
    let representation =
        if union then ValueRepresentation.Union(["None", []; "Some", [componentValue]], Some(1, 1, 1))
        else ValueRepresentation.Record(["Work", componentValue; "Flag", ValueRepresentation.Scalar SettledSlot.Bool], Some([0; 0], 1, 1))
    let raw = revision held
    let graph =
        { raw with
            Codata = { raw.Codata with CallableCarriers = carriers; Escapes = Map.ofList [aggregate.Id, EscapeKind.StackScoped] }
            Emission =
                { raw.Emission with
                    Callable =
                        { raw.Emission.Callable with
                            Contracts = Map.ofList [contract.Identity, contract]; Carriers = carriers
                            AggregateSlots = Map.ofList [slot.Identity, slot]
                            AggregateValues = Map.ofList [aggregate.Id, [construction]; read.Id, [projection]]
                            AggregateDependencies = Map.ofList [aggregate.Id, account construction; read.Id, account projection]
                            Declarations = Map.ofList [implementation.Id, declaration]
                            Symbols = Map.ofList [implementation.Id, declaration.Name]
                            ValueShapes = Map.ofList [formal.Id, CallableValueShape.Data formal.Id; body.Id, CallableValueShape.Data body.Id]
                            ClosedData = Set.ofList [formal.Id; body.Id]
                            AliasTargets = held |> List.map (fun value -> value.Id, value.Id) |> Map.ofList }
                    Numeric =
                        { raw.Emission.Numeric with
                            SourceTypes = held |> List.map (fun value -> value.Id, value.Type) |> Map.ofList
                            Layouts =
                                if union then Map.ofList [aggregateType, SettledLayout.Union(["None", None; "Some", Some(SettledSlot.InlineBytes(0, 1))], Some 1, Some 1, Some 1)]
                                else Map.empty
                            OccurrenceRepresentations =
                                Map.ofList [formal.Id, Result.Ok(ValueRepresentation.Scalar SettledSlot.Bool)
                                            body.Id, Result.Ok(ValueRepresentation.Scalar SettledSlot.Bool)
                                            flag.Id, Result.Ok(ValueRepresentation.Scalar SettledSlot.Bool)
                                            aggregate.Id, Result.Ok representation] } } }
        |> declareTraversalReadings
    let operands = MLIRAccumulator.empty ()
    Operands.bind (context graph code.Id operands) code.Id { SSA = Arg 0; Type = TFunc([TInt(IntWidth 1)], [TInt(IntWidth 1)]) } None |> good
    MLIRAccumulator.bindNode flag.Id (Arg 1) (TInt(IntWidth 1)) operands
    graph, aggregate, read, operands

let private observe union (graph: Revision) (held: SemanticNode) operands =
    let witness = if union then Alex.Witnesses.DUWitness.nanopass else Alex.Witnesses.RecordWitness.nanopass
    witness.Witness (context graph held.Id operands) held

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``closed aggregate components keep code outside data storage`` union =
    let graph, aggregate, read, operands = fixture union
    let construction = observe union graph aggregate operands
    let storage =
        match construction.Result with
        | TRValue value -> value
        | other -> failwithf "Aggregate construction did not produce its data view: %A" other
    MLIRAccumulator.bindNode aggregate.Id storage.SSA storage.Type operands
    let projected = observe union graph read operands
    match projected.Result with
    | TRCallable value ->
        Assert.Equal(TFunc([TInt(IntWidth 1)], [TInt(IntWidth 1)]), (Operands.code value).Type)
        Assert.Equal(None, Operands.environment value)
    | other -> failwithf "Aggregate callable was not reconstructed: %A" other
    Assert.Contains(projected.InlineOps, function MLIROp.FuncOp(FuncOp.FuncConstant _) -> true | _ -> false)
    let stores = construction.InlineOps |> List.choose (function
        | MLIROp.MemRefOp(MemRefOp.Store(_, _, _, ty, _))
        | MLIROp.MemRefOp(MemRefOp.StoreAligned(_, _, _, ty, _, _)) -> Some ty
        | _ -> None)
    Assert.DoesNotContain(stores, function TFunc _ -> true | _ -> false)
    Assert.DoesNotContain(projected.InlineOps, function MLIROp.MemRefOp(MemRefOp.Load _) | MLIROp.MemRefOp(MemRefOp.LoadAligned _) -> true | _ -> false)
    Assert.Empty(operands.Errors)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``aggregate projection rejects a changed formation account without output or operand binding`` union =
    let graph, aggregate, read, operands = fixture union
    MLIRAccumulator.bindNode aggregate.Id (Arg 2) (TMemRefStatic(1, TInt(IntWidth 8))) operands
    let current = graph.Emission.Callable.Carriers[NodeId 3]
    let changed = { current with Formation = NodeId 6 }
    let graph = { graph with Emission = { graph.Emission with Callable = { graph.Emission.Callable with Carriers = graph.Emission.Callable.Carriers.Add(NodeId 3, changed) } } }
    let result = observe union graph read operands
    match result.Result with
    | TRError diagnostic -> Assert.Contains("changed formation", diagnostic.Message)
    | other -> failwithf "Changed formation was accepted: %A" other
    Assert.Empty(result.InlineOps)
    Assert.Empty(result.TopLevelOps)
    Assert.Equal(None, MLIRAccumulator.recallCallable read.Id operands)

/// Two formations share one implementation and physical convention while
/// retaining different actual environment operands. The fixture states their
/// common descriptor placement; Alex is never asked to choose that placement.
let private capturedFixture union selected =
    let graph, aggregate, read, _ = fixture union
    let envType = arrayOf uint8Type
    let envFormal = node 7 (SemanticKind.PatternBinding "environment") envType [] None
    let firstEnv = node 8 (SemanticKind.EnvironmentCreate(NodeId 3, [NodeId 6, NodeId 6])) envType [] None
    let secondEnv = node 9 (SemanticKind.EnvironmentCreate(NodeId 10, [NodeId 6, NodeId 6])) envType [] None
    let first = { graph.Nodes[NodeId 3] with Kind = SemanticKind.ClosureValue(NodeId 2, firstEnv.Id); Children = [NodeId 2; firstEnv.Id] }
    let second = node 10 (SemanticKind.ClosureValue(NodeId 2, secondEnv.Id)) first.Type [2; 9] None
    let parameters = ["environment", envType, envFormal.Id; "value", boolType, NodeId 0]
    let implementation =
        { graph.Nodes[NodeId 2] with
            Kind = SemanticKind.Lambda(parameters, NodeId 1, [], None, LambdaContext.RegularClosure)
            Type = functionFrom envType first.Type
            Children = [envFormal.Id; NodeId 0; NodeId 1] }
    let carrier source environment =
        { graph.Emission.Callable.Carriers[NodeId 3] with
            Occurrence = source; Formation = source; EnvironmentValue = Some environment
            Parameters = parameters; ParameterShapes = [CallableValueShape.Data envFormal.Id; CallableValueShape.Data(NodeId 0)]
            Environment = Some { Owner = source; Formal = envFormal.Id } }
    let firstCarrier, secondCarrier = carrier first.Id firstEnv.Id, carrier second.Id secondEnv.Id
    let carriers = Map.ofList [first.Id, firstCarrier; second.Id, secondCarrier]
    let contract =
        { graph.Emission.Callable.Contracts[NodeId 2] with
            ParameterTypes = [envType; boolType]
            EnvironmentBytes = Some 1
            ParameterRepresentations =
                [0, ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
                 1, ValueRepresentation.Scalar SettledSlot.Bool] }
    let slot = graph.Emission.Callable.AggregateSlots[NodeId 99]
    let alternative ordinal (carrier: CallableCarrier) : CallableAggregateAlternative =
        { Ordinal = ordinal; Carrier = carrier.Occurrence; Formation = carrier.Formation
          EnvironmentValue = carrier.EnvironmentValue; Contract = contract.Identity; Adapter = None
          EnvironmentPlacement = Some { Value = carrier.EnvironmentValue.Value; Owner = carrier.Occurrence
                                        Source = CallableAggregateEnvironmentSource.EnvironmentValue
                                        ViewBytes = 1; ByteOffset = 8; StorageBytes = 40; Alignment = 8; Adaptation = None } }
    let alternatives = [alternative 0 firstCarrier; alternative 1 secondCarrier]
    let originals = graph.Emission.Callable.AggregateValues
    let update (row: CallableAggregateValue) =
        { row with Alternatives = alternatives; Bytes = 48; Alignment = 8
                   Selector = Some { Lower = 0; UpperExclusive = 2; Storage = Some aggregate.Id
                                     Slot = Some(SettledSlot.Integer(8, None)); ByteOffset = Some 0 }
                   FormationInputs = [first.Id; second.Id] }
    let written = if selected = 0 then first.Id else second.Id
    let construction = { update originals[aggregate.Id].Head with Value = Some written; SelectedAlternative = Some selected }
    let projection = update originals[read.Id].Head
    let flow : CallableFlow =
        { Occurrence = read.Id; SourceType = read.Type; Alternatives = [first.Id; second.Id]
          Dependencies = Map.empty; Calls = [] }
    let account (value: CallableAggregateValue) : CallableAggregateDependencyAccount =
        { Occurrence = value.Occurrence; Slots = [slot]; Values = [value]; Carriers = [firstCarrier; secondCarrier]
          Contracts = [contract]; Flows = [flow]; Joins = []; Participants = []; Sources = []; Claims = [] }
    let capture : ContinuationSlot =
        { Source = NodeId 6; ValueType = boolType; IsCapture = true; Holds = CaptureSlotKind.Scalar SettledSlot.Bool
          Field = { Name = "flag"; Slot = SettledSlot.Bool; Offset = Some 0; Size = Some 1; Align = Some 1 } }
    let layout owner : EnvironmentLayout =
        { Owner = owner; Implementation = implementation.Id; Formal = envFormal.Id; Slots = [capture]
          Bytes = 1; Alignment = 1; Obligations = [] }
    let componentData =
        ValueRepresentation.Record(
            ["selector", ValueRepresentation.Scalar(SettledSlot.Integer(8, None))
             "environment", ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))],
            Some([0; 8], 48, 8))
    let componentValue = ValueRepresentation.CallableComponent(slot.Identity, componentData)
    let representation =
        if union then ValueRepresentation.Union(["None", []; "Some", [componentValue]], Some(8, 56, 8))
        else ValueRepresentation.Record(["Work", componentValue; "Flag", ValueRepresentation.Scalar SettledSlot.Bool], Some([0; 48], 56, 8))
    let graph =
        { graph with
            Nodes = [implementation; first; second; envFormal; firstEnv; secondEnv] |> List.fold (fun nodes value -> Map.add value.Id value nodes) graph.Nodes
            Codata =
                { graph.Codata with CallableCarriers = carriers
                                    EnvironmentLayouts = Map.ofList [first.Id, layout first.Id; second.Id, layout second.Id]
                                    EnvironmentOrigins = Map.ofList [first.Id, first.Id; second.Id, second.Id]
                                    KnownCallables =
                                        Map.ofList
                                            [ first.Id, { Implementation = implementation.Id; EnvironmentOwner = first.Id }
                                              second.Id, { Implementation = implementation.Id; EnvironmentOwner = second.Id } ] }
            Emission =
                { graph.Emission with
                    Callable =
                        { graph.Emission.Callable with Carriers = carriers; Contracts = Map.ofList [contract.Identity, contract]
                                                       Flows = Map.ofList [read.Id, flow]
                                                       AggregateValues = Map.ofList [aggregate.Id, [construction]; read.Id, [projection]]
                                                       AggregateDependencies = Map.ofList [aggregate.Id, account construction; read.Id, account projection]
                                                       ValueShapes = graph.Emission.Callable.ValueShapes.Add(envFormal.Id, CallableValueShape.Data envFormal.Id)
                                                       ClosedData = graph.Emission.Callable.ClosedData.Add envFormal.Id
                                                       Declarations = Map.ofList [implementation.Id, { graph.Emission.Callable.Declarations[implementation.Id] with Parameters = parameters }] }
                    Numeric =
                        { graph.Emission.Numeric with
                            OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations
                                                            .Add(envFormal.Id, Result.Ok(ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))))
                                                            .Add(aggregate.Id, Result.Ok representation) } } }
        |> declareTraversalReadings
    let operands = MLIRAccumulator.empty ()
    let functionType = TFunc([TMemRefStatic(1, TInt(IntWidth 8)); TInt(IntWidth 1)], [TInt(IntWidth 1)])
    for source, ordinal in [first.Id, 0; second.Id, 1] do
        Operands.bind (context graph source operands) source { SSA = Arg(ordinal * 2); Type = functionType }
                      (Some { SSA = Arg(ordinal * 2 + 1); Type = TMemRefStatic(1, TInt(IntWidth 8)) }) |> good
    MLIRAccumulator.bindNode aggregate.Id (Arg 4) (TMemRefStatic(56, TInt(IntWidth 8))) operands
    graph, aggregate, read, operands

[<Theory>]
[<InlineData(false, 0)>]
[<InlineData(false, 1)>]
[<InlineData(true, 0)>]
[<InlineData(true, 1)>]
let ``aggregate writes preserve the selected actual environment and reads reconstruct paired operands`` union selected =
    let graph, aggregate, read, operands = capturedFixture union selected
    let writes =
        let pattern = Alex.Patterns.CallableAggregatePatterns.pWriteComponents (context graph aggregate.Id operands) aggregate.Id aggregate.Id
                          { SSA = Arg 4; Type = TMemRefStatic(56, TInt(IntWidth 8)) }
        match matchAt pattern (focus graph aggregate) 64 operands with
        | Result.Ok(operations, _) -> operations
        | Result.Error reason -> failwith reason
    let environmentStores = writes |> List.choose (function
        | MLIROp.MemRefOp(MemRefOp.StoreAligned(value, _, _, (TMemRefStatic(1, TInt(IntWidth 8)) as ty), _, _)) -> Some(value, ty)
        | _ -> None)
    Assert.Equal((Arg(selected * 2 + 1), TMemRefStatic(1, TInt(IntWidth 8))), Assert.Single environmentStores)
    let output = observe union graph read operands
    match output.Result with
    | TRCallable value ->
        Assert.Equal(Some(TMemRefStatic(1, TInt(IntWidth 8))), Operands.environment value |> Option.map _.Type)
        Assert.NotEqual((Operands.code value).SSA, (Operands.environment value).Value.SSA)
    | other -> failwithf "Paired aggregate projection failed: %A" other
    let selectorLoads = output.InlineOps |> List.choose (function
        | MLIROp.MemRefOp(MemRefOp.LoadAligned(_, _, _, TInt(IntWidth 8), _, _)) -> Some ()
        | _ -> None)
    Assert.Single selectorLoads |> ignore
    let selections = output.InlineOps |> List.choose (function
        | MLIROp.SCFOp(SCFOp.If(_, _, _, Some(_, ty))) -> Some ty
        | _ -> None)
    Assert.Equal(2, selections.Length)
    Assert.Empty(operands.Errors)

[<Fact>]
let ``absent callable Result case retains the selected scalar payload without inventing a contract`` () =
    let callableType = functionFrom boolType boolType
    let resultType =
        TypeIdentity.Application(
            { Declaration = { Module = []; Name = "result" }; Parameters = [TypeParamKind.Type; TypeParamKind.Type]; NativeKind = None },
            [callableType; boolType])
    let destination = node 0 (SemanticKind.PatternBinding "destination") resultType [] None
    let payload = node 1 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let initialization = node 2 (SemanticKind.DUInitialize(destination.Id, "Error", 1, Some payload.Id)) unitType [0; 1] None
    let slot : CallableAggregateSlot =
        { Identity = NodeId 99; AggregateType = resultType; Declaration = None; DeclarationFacts = []
          Path = [CallableAggregatePathStep.UnionPayload(0, 0)]; SourceType = callableType
          Contract = Result.Error "The absent Ok case has no formed callable family."; Participants = [] }
    let row : CallableAggregateValue =
        { Occurrence = initialization.Id; Aggregate = destination.Id; Slot = slot.Identity
          Alternatives = []; Selector = None; FormationInputs = []; Value = None; SelectedAlternative = None
          Operation = CallableAggregateOperation.Construct; Frontier = None
          Tag = Some { Constructor = initialization.Id; TagRead = None; CaseOrdinal = 1
                       PayloadOrdinal = Some 0; Payload = Some payload.Id; Participants = [] }
          Bytes = 0; Alignment = 1; Participants = [] }
    let account : CallableAggregateDependencyAccount =
        { Occurrence = initialization.Id; Slots = [slot]; Values = [row]; Carriers = []; Contracts = []
          Flows = []; Joins = []; Participants = []; Sources = []; Claims = [] }
    let held = [destination; payload; initialization]
    let raw = revision held
    let graph =
        { raw with
            Emission =
                { raw.Emission with
                    Callable =
                        { raw.Emission.Callable with
                            AggregateSlots = Map.ofList [slot.Identity, slot]
                            AggregateValues = Map.ofList [initialization.Id, [row]]
                            AggregateDependencies = Map.ofList [initialization.Id, account]
                            AliasTargets = held |> List.map (fun value -> value.Id, value.Id) |> Map.ofList }
                    Numeric =
                        { raw.Emission.Numeric with
                            SourceTypes = held |> List.map (fun value -> value.Id, value.Type) |> Map.ofList
                            Layouts = Map.ofList [resultType, SettledLayout.Union(["Ok", Some(SettledSlot.InlineBytes(0, 1)); "Error", Some SettledSlot.Bool], Some 1, Some 2, Some 1)] } } }
        |> declareTraversalReadings
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode destination.Id (Arg 0) (TMemRefStatic(2, TInt(IntWidth 8))) operands
    MLIRAccumulator.bindNode payload.Id (Arg 1) (TInt(IntWidth 1)) operands
    let pattern =
        Alex.Patterns.DUPatterns.pBuildDUComponentInitialize (context graph initialization.Id operands)
            initialization.Id destination.Id "Error" 1 (Some payload.Id)
    let operations =
        match matchAt pattern (focus graph initialization) 64 operands with
        | Result.Ok((operations, TRVoid), _) -> operations
        | other -> failwithf "Absent callable case dropped its scalar payload: %A" other
    Assert.Contains(operations, function
        | MLIROp.MemRefOp(MemRefOp.StoreAligned(Arg 1, _, _, TInt(IntWidth 1), _, _)) -> true
        | _ -> false)
    Assert.DoesNotContain(operations, function MLIROp.FuncOp(FuncOp.FuncConstant _) -> true | _ -> false)
    Assert.Empty(graph.Emission.Callable.Contracts)
    Assert.Empty(operands.Errors)
