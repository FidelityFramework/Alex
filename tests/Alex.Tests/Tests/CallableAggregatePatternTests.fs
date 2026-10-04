module Alex.Tests.CallableAggregatePatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
module Operands = Alex.Traversal.CallableOperands
module Zipper = Alex.Traversal.PSGZipper

let private good = function Result.Ok value -> value | Result.Error reason -> failwith reason

let private p role ordinal group identity : Participant =
    { Role = role; Ordinal = ordinal; Group = group; Node = identity }

let private valueParticipants (row: CallableAggregateValue) =
    [ yield p ParticipantRole.AggregateValue 0 row.Occurrence row.Occurrence
      yield p ParticipantRole.AggregateSource 0 row.Occurrence row.Aggregate
      yield p ParticipantRole.AggregateSlot 0 row.Occurrence row.Slot
      for ordinal, input in List.indexed row.FormationInputs do
          yield p ParticipantRole.AggregateInput ordinal row.Occurrence input
      for actual in Option.toList row.Value do yield p ParticipantRole.AggregateWrite 0 row.Occurrence actual
      for frontier in Option.toList row.Frontier do yield p ParticipantRole.AggregateReadFrontier 0 row.Occurrence frontier
      for storage in row.Selector |> Option.bind _.Storage |> Option.toList do
          yield p ParticipantRole.AggregateSelector 0 row.Occurrence storage
      for alternative in row.Alternatives do
          yield p ParticipantRole.CallableCarrier alternative.Ordinal row.Occurrence alternative.Carrier
          yield p ParticipantRole.CallableFormation alternative.Ordinal row.Occurrence alternative.Formation
          yield p ParticipantRole.CallableContract alternative.Ordinal row.Occurrence alternative.Contract
          for environment in Option.toList alternative.EnvironmentValue do
              yield p ParticipantRole.CallableEnvironment alternative.Ordinal row.Occurrence environment ]

/// Fixture authoring from explicitly supplied rows, with no source semantic
/// settlement. Controls that renew copied rows after a mutation say so: they
/// isolate operation binding from the earlier dependency-copy equality guard.
let private withAccounts (graph: Revision) =
    let c = graph.Emission.Callable
    let account occurrence =
        let rec closure seen pending values =
            match pending with
            | [] -> values
            | site :: rest when Set.contains site seen -> closure seen rest values
            | site :: rest ->
                let rows = c.AggregateValues.TryFind site |> Option.defaultValue []
                closure (Set.add site seen) (rest @ (rows |> List.collect _.FormationInputs)) (values @ rows)
        let values = closure Set.empty [occurrence] []
        let slots = values |> List.map _.Slot |> List.distinct |> List.map (fun id -> c.AggregateSlots[id])
        let carriers = values |> List.collect _.Alternatives |> List.collect (fun row -> row.Carrier :: Option.toList row.Adapter)
                       |> List.distinct |> List.map (fun id -> c.Carriers[id])
        let contracts =
            (slots |> List.choose (fun row -> Result.toOption row.Contract)) @
            (carriers |> List.choose (fun row -> Result.toOption row.Contract))
            |> List.distinct |> List.map (fun id -> c.Contracts[id])
        let inputs = values |> List.collect (fun row -> row.Occurrence :: row.FormationInputs) |> List.distinct
        let participants =
            (slots |> List.collect _.Participants) @
            (values |> List.collect (fun row -> row.Participants @ (row.Tag |> Option.map _.Participants |> Option.defaultValue []))) @
            (carriers |> List.collect _.Lifetime) @ (contracts |> List.collect _.Participants)
        let ids = participants |> List.map _.Node |> List.distinct
        let premises = contracts |> List.collect (fun row -> row.SourcePremises.Keys |> Seq.toList) |> Set.ofList
        let sources = ids |> List.choose (fun id ->
            (if premises.Contains id then None else graph.Nodes.TryFind id) |> Option.map (fun node ->
                { Node = id; Kind = node.Kind; Type = node.Type; Children = node.Children; Anchors = node.ObligationAnchors }))
        let implementationIds =
            (carriers |> List.map _.Implementation) @
            (participants |> List.choose (fun row -> if row.Role = ParticipantRole.CallableImplementation then Some row.Node else None))
            |> List.distinct
        { Occurrence = occurrence; Slots = slots; Values = values; Carriers = carriers; Contracts = contracts
          Flows = inputs |> List.choose c.Flows.TryFind; Joins = inputs |> List.choose c.Joins.TryFind
          Participants = participants; Sources = sources
          Claims = ids |> List.choose (fun id -> graph.CurrentClaims.TryFind id |> Option.map (fun row -> id, row))
          Symbols = implementationIds |> List.choose (fun id -> c.Symbols.TryFind id |> Option.map (fun name -> id, name))
          Inactivity = [] }
    let callable = { c with AggregateDependencies = c.AggregateValues |> Map.map (fun occurrence _ -> account occurrence) }
    let codata =
        { graph.Codata with CallableContracts = callable.Contracts; CallableCarriers = callable.Carriers
                            CallableFlows = callable.Flows
                            CallableAggregateSlots = callable.AggregateSlots; CallableAggregateValues = callable.AggregateValues
                            CallableAggregateDependencies = callable.AggregateDependencies }
    { graph with Codata = codata; Emission = { graph.Emission with Callable = callable } }

/// Declare this fixture's complete published value inventory. Callable sites
/// are supplied explicitly: code has an error data representation, never an
/// address-sized scalar. Every data representation must already be stated.
let private publishInventory callableSites supportRows (graph: Revision) =
    let callableSites = callableSites |> List.map NodeId |> Set.ofList
    let supports = supportRows |> List.map (fun (site, inputs) -> NodeId site, inputs |> List.map NodeId |> Set.ofList) |> Map.ofList
    Assert.Equal<Set<NodeId>>(graph.Nodes.Keys |> Set.ofSeq, supports.Keys |> Set.ofSeq)
    let callable = graph.Emission.Callable
    let shapes = graph.Nodes |> Map.map (fun id _ ->
        if callableSites.Contains id then CallableValueShape.Callable id else CallableValueShape.Data id)
    let representations =
        graph.Nodes |> Map.fold (fun rows id node ->
            if callableSites.Contains id then
                rows |> Map.add id (Result.Error "A callable remains a function value and has no numeric data representation.")
            else
                match Map.tryFind id rows with
                | Some(Result.Ok _) -> rows
                | _ -> failwithf "Fixture data node %A lacks its explicitly stated representation: %A" id node.Kind)
            graph.Emission.Numeric.OccurrenceRepresentations
    let closedData =
        shapes
        |> Map.toSeq
        |> Seq.choose (fun (id, shape) ->
            match shape with CallableValueShape.Data _ -> Some id | _ -> None)
        |> Set.ofSeq
    let callable =
        { callable with
            ValueShapes = shapes
            Supports = supports
            AliasTargets = graph.Nodes |> Map.map (fun id _ -> id)
            ClosedData = closedData }
    let numeric =
        { graph.Emission.Numeric with
            SourceTypes = graph.Nodes |> Map.map (fun _ node -> node.Type)
            OccurrenceRepresentations = representations }
    { graph with Emission = { graph.Emission with Callable = callable; Numeric = numeric } }

let private requireIntegrity graph =
    let graph = graph |> withAccounts
    let violations = Integrity.check graph
    Assert.True(violations.IsEmpty, sprintf "The positive contract fixture is invalid: %A" violations)
    graph

let private seal callableSites supportRows graph =
    graph |> publishInventory callableSites supportRows |> declareBindingReadings |> requireIntegrity

let private closedSupports =
    [0, [0]; 1, [0; 1]; 2, [0; 1; 2]; 3, [0; 1; 2; 3]
     4, [0; 1; 2; 3; 4; 6]; 5, [0; 1; 2; 3; 4; 5; 6]; 6, [6]]

let private context (graph: Revision) (occurrence: NodeId) operands : WitnessContext =
    let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = operands; RootAccumulator = operands
      ScopeContext = scope; RootScopeContext = scope; Graph = graph
      Zipper = Zipper.create graph occurrence |> require "Missing aggregate occurrence"
      GlobalVisited = visited; TraversalVisited = visited }

/// These published-value fixtures pass the independent public-image reader.
/// They establish Pattern consumption, not acceptance of a Clef source program.
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
          Convention = CallableConvention.Ordinary
          ParameterTypes = [boolType]; OmittedParameters = []
          ParameterRepresentations = [0, ValueRepresentation.Scalar SettledSlot.Bool]
          ResultType = boolType; ResultRepresentation = ValueRepresentation.Scalar SettledSlot.Bool
          EnvironmentBytes = None; SourcePremises = Map.empty
          Participants = [p ParticipantRole.CallableContract 0 implementation.Id implementation.Id
                          p ParticipantRole.CallableImplementation 0 implementation.Id implementation.Id
                          p ParticipantRole.CalleeParameter 0 implementation.Id formal.Id
                          p ParticipantRole.CalleeBody 0 implementation.Id body.Id] }
    let slot : CallableAggregateSlot =
        { Identity = NodeId 99; AggregateType = aggregateType; Declaration = None; DeclarationFacts = []
          Path = [if union then CallableAggregatePathStep.UnionPayload(1, 0) else CallableAggregatePathStep.RecordField 0]
          SourceType = callableType; Contract = Result.Ok contract.Identity
          Participants = [p ParticipantRole.AggregateSlot 0 (NodeId 99) (NodeId 99)
                          p ParticipantRole.CallableContract 0 (NodeId 99) contract.Identity] }
    let alternative : CallableAggregateAlternative =
        { Ordinal = 0; Carrier = code.Id; Formation = implementation.Id; EnvironmentValue = None
          Contract = contract.Identity; Adapter = None; EnvironmentPlacement = None }
    let tag =
        if union then Some { Constructor = aggregate.Id; TagRead = None; CaseOrdinal = 1
                             PayloadOrdinal = Some 0; Payload = Some code.Id
                             Participants = [p ParticipantRole.AggregateConstructor 0 aggregate.Id aggregate.Id
                                             p ParticipantRole.AggregatePayload 0 aggregate.Id code.Id] }
        else None
    let row occurrence operation value selected : CallableAggregateValue =
        { Occurrence = occurrence; Aggregate = aggregate.Id; Slot = slot.Identity
          Alternatives = [alternative]
          Selector = Some { Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None }
          FormationInputs = [if operation = CallableAggregateOperation.Construct then code.Id else aggregate.Id]
          Value = value; SelectedAlternative = selected
          Operation = operation; Frontier = if operation = CallableAggregateOperation.Project then Some occurrence else None
          Tag = tag; Bytes = 0; Alignment = 1; Participants = [] }
        |> fun row -> { row with Participants = valueParticipants row }
    let construction = row aggregate.Id CallableAggregateOperation.Construct (Some code.Id) (Some 0)
    let projection = row read.Id CallableAggregateOperation.Project None None
    let account (value: CallableAggregateValue) : CallableAggregateDependencyAccount =
        { Occurrence = value.Occurrence; Slots = [slot]; Values = [value]; Carriers = List.ofSeq carriers.Values
          Contracts = [contract]; Flows = []; Joins = []; Participants = []; Sources = []; Claims = []; Symbols = []; Inactivity = [] }
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
        |> seal [2; 3; 5] closedSupports
    let operands = MLIRAccumulator.empty ()
    Operands.bind (context graph code.Id operands) code.Id { SSA = Arg 0; Type = TFunc([TInt(IntWidth 1)], [TInt(IntWidth 1)]) } None |> good
    MLIRAccumulator.bindNode flag.Id (Arg 1) (TInt(IntWidth 1)) operands
    graph, aggregate, read, operands

let private observe union (graph: Revision) (held: SemanticNode) operands =
    let witness = if union then Alex.Witnesses.DUWitness.nanopass else Alex.Witnesses.RecordWitness.nanopass
    witness.Witness (context graph held.Id operands) held

let private refused reason (held: SemanticNode) (operands: MLIRAccumulator) (output: WitnessOutput) =
    match output.Result with
    | TRError diagnostic -> Assert.Contains(reason, diagnostic.Message)
    | other -> failwithf "Invalid operation was admitted: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Equal(None, MLIRAccumulator.recallCallable held.Id operands)
    Assert.Equal(None, MLIRAccumulator.recallNode held.Id operands)

/// A negative operation control keeps its declared row and updates only the
/// copied source shape; otherwise the earlier account guard would mask the
/// specific operand-binding check being tested.
let private changeOperation (graph: Revision) (held: SemanticNode) kind =
    let changed = { held with Kind = kind }
    let graph = { graph with Nodes = graph.Nodes.Add(held.Id, changed) }
    let accounts = graph.Emission.Callable.AggregateDependencies |> Map.map (fun _ account ->
        let sources = account.Sources |> List.map (fun source ->
            if source.Node = held.Id then { source with Kind = kind } else source)
        { account with Sources = sources })
    let callable = { graph.Emission.Callable with AggregateDependencies = accounts }
    let codata = { graph.Codata with CallableAggregateDependencies = accounts }
    { graph with Codata = codata; Emission = { graph.Emission with Callable = callable } }, changed

[<Theory>]
[<InlineData("record-field")>]
[<InlineData("record-aggregate")>]
[<InlineData("record-value")>]
[<InlineData("record-assignment")>]
[<InlineData("union-case")>]
[<InlineData("union-constructor")>]
[<InlineData("union-payload")>]
[<InlineData("union-initialize")>]
let ``callable aggregate operation binds the exact witnessed operands`` (variant: string) =
    let union = variant.StartsWith "union-"
    let graph, aggregate, read, operands = fixture union
    let held, kind, reason =
        match variant with
        | "record-field" -> read, SemanticKind.FieldGet(aggregate.Id, "Flag"), "Callable record projection differs"
        | "record-aggregate" -> read, SemanticKind.FieldGet(NodeId 6, "Work"), "Callable record projection differs"
        | "record-value" -> aggregate, SemanticKind.RecordExpr(["Work", NodeId 6; "Flag", NodeId 6], None), "witnessed field operand"
        | "record-assignment" -> read, SemanticKind.FieldSet(aggregate.Id, "Work", NodeId 6), "Callable record assignment differs"
        | "union-case" -> read, SemanticKind.DUEliminate(aggregate.Id, 0, "None", read.Type), "Callable union projection differs"
        | "union-constructor" -> aggregate, SemanticKind.DUConstruct("None", 0, Some(NodeId 3), None), "witnessed constructor, tag or payload"
        | "union-payload" -> aggregate, SemanticKind.DUConstruct("Some", 1, Some(NodeId 6), None), "witnessed constructor, tag or payload"
        | "union-initialize" -> aggregate, SemanticKind.DUInitialize(aggregate.Id, "Some", 1, Some(NodeId 3)), "no explicit source-authored transport relation"
        | other -> failwith other
    let changed, held = changeOperation graph held kind
    observe union changed held operands |> refused reason held operands

[<Fact>]
let ``ordinary field projection in a mixed record remains ordinary`` () =
    let graph, aggregate, _, operands = fixture false
    let flagRead = node 22 (SemanticKind.FieldGet(aggregate.Id, "Flag")) boolType [4] None
    let numeric =
        { graph.Emission.Numeric with
            OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations.Add(flagRead.Id, Result.Ok(ValueRepresentation.Scalar SettledSlot.Bool)) }
    let graph =
        { graph with Nodes = graph.Nodes.Add(flagRead.Id, flagRead); Emission = { graph.Emission with Numeric = numeric } }
        |> seal [2; 3; 5] (closedSupports @ [22, [4; 6; 22]])
    Assert.Empty(Integrity.check graph)
    let aggregateType = mapTypeAt aggregate.Id (context graph flagRead.Id operands)
    MLIRAccumulator.bindNode aggregate.Id (Arg 2) aggregateType operands
    let output = observe false graph flagRead operands
    match output.Result with
    | TRValue value -> Assert.Equal(TInt(IntWidth 1), value.Type)
    | other -> failwithf "Ordinary record field was routed as callable: %A" other
    Assert.DoesNotContain(output.InlineOps, function MLIROp.FuncOp(FuncOp.FuncConstant _) -> true | _ -> false)

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

/// Published two-arm controls use distinct implementations and environment
/// placements. They exercise passive transport of supplied value evidence;
/// source selection and retained-environment lifetime are not claimed here.
let private capturedFixture union selected =
    let graph, aggregate, read, _ = fixture union
    let envType = arrayOf uint8Type
    let envFormal = node 7 (SemanticKind.PatternBinding "environment") envType [] None
    let firstEnv = node 8 (SemanticKind.EnvironmentCreate(NodeId 3, [NodeId 6, NodeId 6])) envType [] None
    let secondEnv = node 9 (SemanticKind.EnvironmentCreate(NodeId 10, [NodeId 6, NodeId 6])) envType [] None
    let first = { graph.Nodes[NodeId 3] with Kind = SemanticKind.ClosureValue(NodeId 2, firstEnv.Id); Children = [NodeId 2; firstEnv.Id] }
    let second = node 10 (SemanticKind.ClosureValue(NodeId 11, secondEnv.Id)) first.Type [11; 9] None
    let secondBody = node 12 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let secondFormal = node 13 (SemanticKind.PatternBinding "value") boolType [] None
    let secondEnvFormal = node 14 (SemanticKind.PatternBinding "environment") envType [] None
    let parameters = ["environment", envType, envFormal.Id; "value", boolType, NodeId 0]
    let implementation =
        { graph.Nodes[NodeId 2] with
            Kind = SemanticKind.Lambda(parameters, NodeId 1, [], None, LambdaContext.RegularClosure)
            Type = functionFrom envType first.Type
            Children = [envFormal.Id; NodeId 0; NodeId 1] }
    let secondParameters = ["environment", envType, secondEnvFormal.Id; "value", boolType, secondFormal.Id]
    let secondImplementation =
        node 11 (SemanticKind.Lambda(secondParameters, secondBody.Id, [], None, LambdaContext.RegularClosure))
            implementation.Type [14; 13; 12] None
    let carrier source environment implementation parameters (environmentFormal: SemanticNode) result =
        { graph.Emission.Callable.Carriers[NodeId 3] with
            Occurrence = source; Formation = source; EnvironmentValue = Some environment
            Implementation = implementation
            Parameters = parameters; ParameterShapes = parameters |> List.map (fun (_, _, formal) -> CallableValueShape.Data formal)
            Result = result; ResultShape = CallableValueShape.Data result
            Lifetime = [p ParticipantRole.CallableLifetime 0 source environment]
            Environment = Some { Owner = source; Formal = environmentFormal.Id } }
    let firstCarrier = carrier first.Id firstEnv.Id implementation.Id parameters envFormal (NodeId 1)
    let secondCarrier = carrier second.Id secondEnv.Id secondImplementation.Id secondParameters secondEnvFormal secondBody.Id
    let carriers = Map.ofList [first.Id, firstCarrier; second.Id, secondCarrier]
    let contract =
        { graph.Emission.Callable.Contracts[NodeId 2] with
            ParameterTypes = [envType; boolType]
            EnvironmentBytes = Some 1
            Participants = [p ParticipantRole.CallableContract 0 implementation.Id implementation.Id
                            p ParticipantRole.CallableImplementation 0 implementation.Id implementation.Id
                            p ParticipantRole.CalleeParameter 0 implementation.Id envFormal.Id
                            p ParticipantRole.CalleeParameter 1 implementation.Id (NodeId 0)
                            p ParticipantRole.CalleeBody 0 implementation.Id (NodeId 1)]
            ParameterRepresentations =
                [0, ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
                 1, ValueRepresentation.Scalar SettledSlot.Bool] }
    let slot = graph.Emission.Callable.AggregateSlots[NodeId 99]
    let alternative ordinal (carrier: CallableCarrier) : CallableAggregateAlternative =
        { Ordinal = ordinal; Carrier = carrier.Occurrence; Formation = carrier.Formation
          EnvironmentValue = carrier.EnvironmentValue; Contract = contract.Identity; Adapter = None
          EnvironmentPlacement = Some { Value = carrier.EnvironmentValue.Value; Owner = carrier.Occurrence
                                        Source = CallableAggregateEnvironmentSource.EnvironmentValue
                                        ViewBytes = 1; ByteOffset = 8 + ordinal * 40; StorageBytes = 40; Alignment = 8; Adaptation = None } }
    let alternatives = [alternative 0 firstCarrier; alternative 1 secondCarrier]
    let originals = graph.Emission.Callable.AggregateValues
    let update (row: CallableAggregateValue) =
        { row with Alternatives = alternatives; Bytes = 88; Alignment = 8
                   Selector = Some { Lower = 0; UpperExclusive = 2; Storage = Some aggregate.Id
                                     Slot = Some(SettledSlot.Integer(8, None)); ByteOffset = Some 0 }
                   FormationInputs = if row.Operation = CallableAggregateOperation.Construct then [first.Id; second.Id] else [aggregate.Id] }
    let written = if selected = 0 then first.Id else second.Id
    let construction = { update originals[aggregate.Id].Head with Value = Some written; SelectedAlternative = Some selected }
    let projection = update originals[read.Id].Head
    let withTag (row: CallableAggregateValue) =
        let tag = row.Tag |> Option.map (fun tag ->
            { tag with Payload = Some written
                       Participants = [p ParticipantRole.AggregateConstructor 0 aggregate.Id aggregate.Id
                                       p ParticipantRole.AggregatePayload 0 aggregate.Id written] })
        let tagged = { row with Tag = tag }
        { tagged with Participants = valueParticipants tagged }
    let construction, projection = withTag construction, withTag projection
    let aggregate =
        if union then { aggregate with Kind = SemanticKind.DUConstruct("Some", 1, Some written, None); Children = [written] }
        else { aggregate with Kind = SemanticKind.RecordExpr(["Work", written; "Flag", NodeId 6], None); Children = [written; NodeId 6] }
    let flow : CallableFlow =
        { Occurrence = read.Id; SourceType = read.Type; Alternatives = [first.Id; second.Id]
          Dependencies = Map.empty; Calls = [] }
    let account (value: CallableAggregateValue) : CallableAggregateDependencyAccount =
        { Occurrence = value.Occurrence; Slots = [slot]; Values = [value]; Carriers = [firstCarrier; secondCarrier]
          Contracts = [contract]; Flows = [flow]; Joins = []; Participants = []; Sources = []; Claims = []; Symbols = []; Inactivity = [] }
    let capture : ContinuationSlot =
        { Source = NodeId 6; ValueType = boolType; IsCapture = true; Holds = CaptureSlotKind.Scalar SettledSlot.Bool
          Field = { Name = "flag"; Slot = SettledSlot.Bool; Offset = Some 0; Size = Some 1; Align = Some 1 } }
    let layout owner implementation formal : EnvironmentLayout =
        { Owner = owner; Implementation = implementation; Formal = formal; Slots = [capture]
          Bytes = 1; Alignment = 1; Obligations = [] }
    let componentData =
        ValueRepresentation.Record(
            ["component0", ValueRepresentation.Scalar(SettledSlot.Integer(8, None))
             "component1", ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
             "component2", ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))],
            Some([0; 8; 48], 88, 8))
    let componentValue = ValueRepresentation.CallableComponent(slot.Identity, componentData)
    let representation =
        if union then ValueRepresentation.Union(["None", []; "Some", [componentValue]], Some(8, 96, 8))
        else ValueRepresentation.Record(["Work", componentValue; "Flag", ValueRepresentation.Scalar SettledSlot.Bool], Some([0; 88], 96, 8))
    let firstDeclaration =
        { graph.Emission.Callable.Declarations[implementation.Id] with
            Parameters = parameters
            Name = CallableSymbolName.RootBinding "first"
            Participants = Set.ofList [implementation.Id; envFormal.Id; NodeId 0; NodeId 1] }
    let secondDeclaration =
        { firstDeclaration with Lookup = secondImplementation.Id; Implementation = secondImplementation.Id
                                Parameters = secondParameters; Result = secondBody.Id; Name = CallableSymbolName.RootBinding "second"
                                Participants = Set.ofList [secondImplementation.Id; secondEnvFormal.Id; secondFormal.Id; secondBody.Id] }
    let graph =
        { graph with
            Nodes = [aggregate; implementation; first; second; envFormal; firstEnv; secondEnv
                     secondImplementation; secondBody; secondFormal; secondEnvFormal] |> List.fold (fun nodes value -> Map.add value.Id value nodes) graph.Nodes
            Codata =
                { graph.Codata with CallableCarriers = carriers
                                    EnvironmentLayouts = Map.ofList [first.Id, layout first.Id implementation.Id envFormal.Id;
                                                                     second.Id, layout second.Id secondImplementation.Id secondEnvFormal.Id]
                                    EnvironmentOrigins = Map.ofList [first.Id, first.Id; second.Id, second.Id]
                                    KnownCallables =
                                        Map.ofList
                                            [ first.Id, { Implementation = implementation.Id; EnvironmentOwner = first.Id }
                                              second.Id, { Implementation = secondImplementation.Id; EnvironmentOwner = second.Id } ] }
            Emission =
                { graph.Emission with
                    Callable =
                        { graph.Emission.Callable with Carriers = carriers; Contracts = Map.ofList [contract.Identity, contract]
                                                       Flows = Map.ofList [read.Id, flow]
                                                       AggregateValues = Map.ofList [aggregate.Id, [construction]; read.Id, [projection]]
                                                       AggregateDependencies = Map.ofList [aggregate.Id, account construction; read.Id, account projection]
                                                       ValueShapes = graph.Emission.Callable.ValueShapes
                                                                        .Add(envFormal.Id, CallableValueShape.Data envFormal.Id)
                                                                        .Add(secondEnvFormal.Id, CallableValueShape.Data secondEnvFormal.Id)
                                                                        .Add(firstEnv.Id, CallableValueShape.Data firstEnv.Id)
                                                                        .Add(secondEnv.Id, CallableValueShape.Data secondEnv.Id)
                                                       ClosedData = graph.Emission.Callable.ClosedData
                                                                        .Add(envFormal.Id).Add(secondEnvFormal.Id).Add(firstEnv.Id).Add(secondEnv.Id)
                                                       Declarations = Map.ofList [implementation.Id, firstDeclaration; secondImplementation.Id, secondDeclaration]
                                                       Symbols = Map.ofList [implementation.Id, firstDeclaration.Name; secondImplementation.Id, secondDeclaration.Name] }
                    Numeric =
                        { graph.Emission.Numeric with
                            Layouts =
                                if union then
                                    graph.Emission.Numeric.Layouts.Add(aggregate.Type,
                                        SettledLayout.Union(["None", None; "Some", Some(SettledSlot.InlineBytes(88, 8))], Some 8, Some 96, Some 8))
                                else graph.Emission.Numeric.Layouts
                            OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations
                                                            .Add(envFormal.Id, Result.Ok(ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))))
                                                            .Add(secondEnvFormal.Id, Result.Ok(ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))))
                                                            .Add(firstEnv.Id, Result.Ok(ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))))
                                                            .Add(secondEnv.Id, Result.Ok(ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))))
                                                            .Add(secondFormal.Id, Result.Ok(ValueRepresentation.Scalar SettledSlot.Bool))
                                                            .Add(secondBody.Id, Result.Ok(ValueRepresentation.Scalar SettledSlot.Bool))
                                                            .Add(aggregate.Id, Result.Ok representation) } } }
        |> fun graph ->
            let numeric = { graph.Emission.Numeric with SourceTypes = graph.Nodes |> Map.map (fun _ node -> node.Type) }
            { graph with Emission = { graph.Emission with Numeric = numeric } }
        |> seal [2; 3; 5; 10; 11]
            [0, [0]; 1, [0; 1]; 2, [0; 1; 2; 7]; 3, [0; 1; 2; 3; 6; 7; 8]
             4, [0 .. 14]; 5, [0 .. 14]; 6, [6]; 7, [7]; 8, [3; 6; 8]; 9, [6; 9; 10]
             10, [6; 9; 10; 11; 12; 13; 14]; 11, [11; 12; 13; 14]
             12, [12]; 13, [13]; 14, [14]]
    let operands = MLIRAccumulator.empty ()
    let functionType = TFunc([TMemRefStatic(1, TInt(IntWidth 8)); TInt(IntWidth 1)], [TInt(IntWidth 1)])
    for source, ordinal in [first.Id, 0; second.Id, 1] do
        Operands.bind (context graph source operands) source { SSA = Arg(ordinal * 2); Type = functionType }
                      (Some { SSA = Arg(ordinal * 2 + 1); Type = TMemRefStatic(1, TInt(IntWidth 8)) }) |> good
    graph, aggregate, read, operands

[<Theory>]
[<InlineData(false, 0)>]
[<InlineData(false, 1)>]
[<InlineData(true, 0)>]
[<InlineData(true, 1)>]
let ``aggregate writes preserve the selected actual environment and reads reconstruct paired operands`` union selected =
    let graph, aggregate, read, operands = capturedFixture union selected
    let writes =
        let pattern = Alex.Patterns.CallableAggregatePatterns.pWriteComponents (context graph aggregate.Id operands) aggregate.Id aggregate.Kind
                          { SSA = Arg 4; Type = TMemRefStatic(96, TInt(IntWidth 8)) }
        match matchAt pattern (focus graph aggregate) 64 operands with
        | Result.Ok(operations, _) -> operations
        | Result.Error reason -> failwith reason
    let environmentStores = writes |> List.choose (function
        | MLIROp.MemRefOp(MemRefOp.StoreAligned(value, _, _, (TMemRefStatic(1, TInt(IntWidth 8)) as ty), _, _)) -> Some(value, ty)
        | _ -> None)
    Assert.Equal((Arg(selected * 2 + 1), TMemRefStatic(1, TInt(IntWidth 8))), Assert.Single environmentStores)
    // M2: follow the stored SSA back to the selector literal. A constant zero
    // implementation fails the selected=1 cases even if an environment stores.
    let selectorStore =
        writes
        |> List.choose (function
            | MLIROp.MemRefOp(MemRefOp.StoreAligned(value, _, _, TInt(IntWidth 8), _, _)) -> Some value
            | _ -> None)
        |> Assert.Single
    let selectorLiteral =
        writes
        |> List.choose (function
            | MLIROp.ArithOp(ArithOp.ConstI(value, ordinal, TInt(IntWidth 8))) when value = selectorStore -> Some ordinal
            | _ -> None)
        |> Assert.Single
    Assert.Equal(int64 selected, selectorLiteral)
    MLIRAccumulator.bindNode aggregate.Id (Arg 4) (TMemRefStatic(96, TInt(IntWidth 8))) operands
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
    // M3: bind both lanes' comparison/yields to the named arm and its distinct
    // environment offset. The final arm also has an explicit comparison and
    // assertion; a fabricated default callable cannot satisfy this control.
    let literal operations name =
        operations
        |> List.choose (function
            | MLIROp.ArithOp(ArithOp.ConstI(result, value, _)) when result = name -> Some value
            | _ -> None)
        |> Assert.Single
    let comparison operations condition =
        operations
        |> List.choose (function
            | MLIROp.ArithOp(ArithOp.CmpI(result, ICmpPred.Eq, _, rhs, _)) when result = condition -> Some rhs
            | _ -> None)
        |> Assert.Single
    let lanes =
        output.InlineOps |> List.choose (function
            | MLIROp.SCFOp(SCFOp.If(condition, firstOps, Some secondOps, Some(_, ty))) -> Some(condition, firstOps, secondOps, ty)
            | _ -> None)
    for condition, firstOps, secondOps, resultType in lanes do
        Assert.Equal(0L, literal output.InlineOps (comparison output.InlineOps condition))
        let finalCondition =
            secondOps
            |> List.choose (function
                | MLIROp.Assert(condition, _) -> Some condition
                | _ -> None)
            |> Assert.Single
        Assert.Equal(1L, literal secondOps (comparison secondOps finalCondition))
        let yielded operations =
            operations
            |> List.choose (function
                | MLIROp.SCFOp(SCFOp.Yield [(value, _)]) -> Some value
                | _ -> None)
            |> Assert.Single
        match resultType with
        | TFunc _ ->
            let symbol operations =
                operations
                |> List.choose (function
                    | MLIROp.FuncOp(FuncOp.FuncConstant(result, name, _)) when result = yielded operations -> Some name
                    | _ -> None)
                |> Assert.Single
            Assert.Equal("first", symbol firstOps)
            Assert.Equal("second", symbol secondOps)
        | TMemRefStatic(1, TInt(IntWidth 8)) ->
            let offset operations =
                Assert.Contains(operations, function
                    | MLIROp.MemRefOp(MemRefOp.LoadAligned(result, _, _, _, _, _)) -> result = yielded operations
                    | _ -> false)
                operations |> List.choose (function MLIROp.ArithOp(ArithOp.ConstI(_, value, TIndex)) -> Some value | _ -> None)
            Assert.Contains(8L, offset firstOps)
            Assert.Contains(48L, offset secondOps)
        | other -> failwithf "Unexpected callable selection lane %A" other
    Assert.Empty(operands.Errors)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``an unselected aggregate alternative is validated before a write`` union =
    let graph, aggregate, _, operands = capturedFixture union 0
    let c = graph.Emission.Callable
    let row = c.AggregateValues[aggregate.Id].Head
    let alternatives = row.Alternatives |> List.map (fun arm ->
        if arm.Ordinal = 1 then { arm with EnvironmentValue = row.Alternatives.Head.EnvironmentValue } else arm)
    let changed = { row with Alternatives = alternatives }
    let changed = { changed with Participants = valueParticipants changed }
    let callable = { c with AggregateValues = c.AggregateValues.Add(aggregate.Id, [changed]) }
    // Keep the copied rows current so this probes the unselected arm's pairing,
    // independently of the earlier dependency-copy equality refusal.
    let graph = { graph with Emission = { graph.Emission with Callable = callable } } |> withAccounts
    observe union graph aggregate operands
    |> refused "lost its paired formation, environment or contract" aggregate operands

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``callable copy refuses omitted inherited fields even when component rows disappear`` allRows =
    let original, aggregate, _, operands = fixture false
    let originalCallable = original.Emission.Callable
    let firstSlot = originalCallable.AggregateSlots[NodeId 99]
    let secondSlot =
        { firstSlot with Identity = NodeId 100; Path = [CallableAggregatePathStep.RecordField 1]
                         Participants = [p ParticipantRole.AggregateSlot 0 (NodeId 100) (NodeId 100)
                                         p ParticipantRole.CallableContract 0 (NodeId 100) (NodeId 2)] }
    let firstRow = originalCallable.AggregateValues[aggregate.Id].Head
    let secondRow = { firstRow with Slot = secondSlot.Identity }
    let secondRow = { secondRow with Participants = valueParticipants secondRow }
    let copySource = node 22 (SemanticKind.PatternBinding "copySource") aggregate.Type [] None
    let aggregate =
        { aggregate with Kind = SemanticKind.RecordExpr(["Work", NodeId 3; "Other", NodeId 3; "Flag", NodeId 6], Some copySource.Id)
                         Children = [NodeId 3; NodeId 3; NodeId 6; copySource.Id] }
    let data = ValueRepresentation.Record([], Some([], 0, 1))
    let representation =
        ValueRepresentation.Record(
            ["Work", ValueRepresentation.CallableComponent(firstSlot.Identity, data)
             "Other", ValueRepresentation.CallableComponent(secondSlot.Identity, data)
             "Flag", ValueRepresentation.Scalar SettledSlot.Bool], Some([0; 0; 0], 1, 1))
    let callable =
        { originalCallable with AggregateSlots = originalCallable.AggregateSlots.Add(secondSlot.Identity, secondSlot)
                                AggregateValues = originalCallable.AggregateValues.Add(aggregate.Id, [firstRow; secondRow]) }
    let numeric =
        { original.Emission.Numeric with SourceTypes = original.Emission.Numeric.SourceTypes.Add(copySource.Id, copySource.Type)
                                         OccurrenceRepresentations = original.Emission.Numeric.OccurrenceRepresentations
                                                                        .Add(aggregate.Id, Ok representation).Add(copySource.Id, Ok representation) }
    let graph =
        { original with Nodes = original.Nodes.Add(copySource.Id, copySource).Add(aggregate.Id, aggregate)
                        Emission = { original.Emission with Callable = callable; Numeric = numeric } }
        |> seal [2; 3; 5]
            ((closedSupports |> List.map (fun (site, inputs) -> site, if site = 4 || site = 5 then inputs @ [22] else inputs)) @ [22, [22]])
    // The complete copy has explicit replacements and valid evidence. The
    // negative then removes the inherited Other field's operation-bound row.
    MLIRAccumulator.bindNode copySource.Id (Arg 7) (TMemRefStatic(1, TInt(IntWidth 8))) operands
    let complete = observe false graph aggregate operands
    match complete.Result with TRValue _ -> () | other -> failwithf "Complete callable copy refused: %A" other
    let changed, aggregate = changeOperation graph aggregate (SemanticKind.RecordExpr(["Work", NodeId 3], Some copySource.Id))
    let c = changed.Emission.Callable
    let values = if allRows then c.AggregateValues.Remove aggregate.Id else c.AggregateValues.Add(aggregate.Id, [firstRow])
    let callable = { c with AggregateValues = values }
    let changed = { changed with Emission = { changed.Emission with Callable = callable } } |> withAccounts
    let fresh = MLIRAccumulator.empty ()
    let output = observe false changed aggregate fresh
    let reason = if allRows then "lacks its current published dependency account" else "operation-bound replacement"
    refused reason aggregate fresh output

[<Fact>]
let ``union projection binds retained tag evidence to the observed case`` () =
    let graph, aggregate, read, operands = fixture true
    let c = graph.Emission.Callable
    let row = c.AggregateValues[read.Id].Head
    let tag = { row.Tag.Value with CaseOrdinal = 0 }
    let changed = { row with Tag = Some tag }
    let callable = { c with AggregateValues = c.AggregateValues.Add(read.Id, [changed]) }
    let graph = { graph with Emission = { graph.Emission with Callable = callable } } |> withAccounts
    MLIRAccumulator.bindNode aggregate.Id (Arg 2) (TMemRefStatic(1, TInt(IntWidth 8))) operands
    observe true graph read operands |> refused "Callable union projection differs" read operands

let private nativeFixture union =
    let original, aggregate, read, _ = fixture union
    let c = original.Emission.Callable
    let ordinaryType = original.Nodes[NodeId 2].Type
    let nativeType =
        TypeIdentity.Application(
            { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [TypeParamKind.Type]; NativeKind = Some NTUKind.NTUfnptr },
            [ordinaryType])
    let aggregateType = if union then optionOf nativeType else aggregate.Type
    let binding = node 20 (SemanticKind.Binding("identity", false, false, None)) ordinaryType [2] (Some 21)
    let scope = { node 21 (SemanticKind.ModuleDef("Native", [binding.Id])) unitType [] None with IsReachable = false }
    let implementation = { original.Nodes[NodeId 2] with Parent = Some binding.Id }
    let code = { original.Nodes[NodeId 3] with Type = nativeType }
    let aggregate = { aggregate with Type = aggregateType }
    let read = { read with Type = nativeType }
    let premise form text numbers references children parent sourceType embedded : BoundarySourcePremise =
        { Shape = { Form = form; Text = text; Numbers = numbers; References = references
                    Children = children; Parent = parent; SourceType = sourceType }
          EmbeddedTypes = embedded; ConstructorFacts = []; Reachable = true; Range = None
          ExternLibrary = None; ExternSymbol = None; HasExtern = false; Metadata = Map.empty }
    let scopePremise = premise "module" ["Native"] [] [binding.Id] [] None unitType []
    let premises =
        Map.ofList [
            scope.Id, { scopePremise with Reachable = false }
            binding.Id, premise "binding" ["identity"; "no-declaration-root"] [0I; 0I] [implementation.Id] [implementation.Id] (Some scope.Id) ordinaryType []
            implementation.Id, premise "lambda" ["RegularClosure"; "value"] [1I; 0I; 0I] [NodeId 0; NodeId 1]
                                   [NodeId 0; NodeId 1] (Some binding.Id) ordinaryType [boolType] ]
    let target : BoundaryPlatformPremise =
        { Id = "alex-native-component"; Description = None; LibraryPath = None; SourcePaths = Set.singleton range.File
          Architecture = Some "x86_64"; OS = Some "linux"; RuntimeClaim = Some RuntimeModel.Libc; Substrate = Some SubstrateKind.CPU
          Dimensions = Map.ofList ["Pointer", 64; "Register", 64]; Representations = Map.empty; EndpointReturns = Map.empty }
    let contract = c.Contracts[NodeId 2]
    let lifetime =
        [scope.Id; binding.Id; implementation.Id] |> List.mapi (fun ordinal id -> p ParticipantRole.CallableLifetime ordinal contract.Identity id)
    let convention =
        CallableConvention.CompilerOwnedPortable {
            Target = target; ParameterConversions = [0, CallableConversion.Identity(ValueRepresentation.Scalar SettledSlot.Bool)]
            ResultConversion = CallableConversion.Identity(ValueRepresentation.Scalar SettledSlot.Bool)
            CodeLifetime = { Module = scope.Id; Binding = binding.Id; Implementation = implementation.Id } }
    let contract =
        { contract with
            Kind = CallableKind.NativeEntry
            Convention = convention
            SourcePremises = premises
            Participants =
                contract.Participants @ lifetime @
                ([scope.Id; binding.Id; implementation.Id] |> List.mapi (fun ordinal id -> p ParticipantRole.Source ordinal contract.Identity id)) }
    let carriers = c.Carriers |> Map.map (fun _ carrier ->
        { carrier with Kind = CallableKind.NativeEntry; SourceType = nativeType; Lifetime = lifetime })
    let slot = { c.AggregateSlots[NodeId 99] with AggregateType = aggregateType; SourceType = nativeType }
    let declaration =
        { c.Declarations[NodeId 2] with Parent = Some binding.Id; Name = CallableSymbolName.ModuleBinding("Native", "identity") }
    let callable =
        { c with Contracts = Map.ofList [contract.Identity, contract]; Carriers = carriers
                 AggregateSlots = Map.ofList [slot.Identity, slot]
                 Declarations = Map.ofList [implementation.Id, declaration]
                 Symbols = Map.ofList [implementation.Id, declaration.Name] }
    let nodes = [scope; binding; implementation; code; aggregate; read] |> List.fold (fun nodes node -> Map.add node.Id node nodes) original.Nodes
    let numeric =
        { original.Emission.Numeric with
            SourceTypes = nodes |> Map.map (fun _ node -> node.Type)
            OccurrenceRepresentations = original.Emission.Numeric.OccurrenceRepresentations.Add(scope.Id, Result.Ok(ValueRepresentation.Scalar SettledSlot.Unit)) }
    let graph =
        { original with Nodes = nodes; Platform = { Register = Ok 64; Pointer = Ok 64 }
                        Emission = { original.Emission with Callable = callable; Numeric = numeric } }
        |> publishInventory [2; 3; 5; 20]
            ((closedSupports |> List.map (fun (site, inputs) -> site, if site >= 2 && site <= 5 then inputs @ [20; 21] else inputs)) @
             [20, [0; 1; 2; 20; 21]; 21, [21]])
        |> declareBindingReadings
        |> fun graph ->
            // After startup, the module is lexical context plus its canonical
            // unit fact, not an inactive executable body in the live image.
            // Its immutable residence premise and declaration port stay held.
            let callable = { graph.Emission.Callable with UnitNodes = graph.Emission.Callable.UnitNodes.Add scope.Id }
            { graph with Nodes = graph.Nodes.Remove scope.Id; Emission = { graph.Emission with Callable = callable } }
        |> requireIntegrity
    graph, aggregate, read

[<Theory>]
[<InlineData(false, false)>]
[<InlineData(false, true)>]
[<InlineData(true, false)>]
[<InlineData(true, true)>]
let ``published native component refuses reconstruction with AX4002 and no output`` union projection =
    let graph, aggregate, read = nativeFixture union
    let operands = MLIRAccumulator.empty ()
    if projection then MLIRAccumulator.bindNode aggregate.Id (Arg 0) (TMemRefStatic(1, TInt(IntWidth 8))) operands
    let held = if projection then read else aggregate
    let output = observe union graph held operands
    match output.Result with
    | TRError diagnostic ->
        Assert.Equal(Some AX4002, diagnostic.Code)
        Assert.Contains("receiving contract is published", diagnostic.Message)
        Assert.Equal(Some held.Id, diagnostic.NodeId)
    | other -> failwithf "Native component unexpectedly reconstructed: %A" other
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Equal(None, MLIRAccumulator.recallCallable held.Id operands)
    Assert.Equal(None, MLIRAccumulator.recallNode held.Id operands)

[<Fact>]
let ``absent callable Result case retains the selected scalar payload without inventing a contract`` () =
    let callableType = functionFrom boolType boolType
    let resultType =
        TypeIdentity.Application(
            { Declaration = { Module = []; Name = "result" }; Parameters = [TypeParamKind.Type; TypeParamKind.Type]; NativeKind = None },
            [callableType; boolType])
    let payload = node 1 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let initialization = node 2 (SemanticKind.DUConstruct("Error", 1, Some payload.Id, None)) resultType [1] None
    let slot : CallableAggregateSlot =
        { Identity = NodeId 99; AggregateType = resultType; Declaration = None; DeclarationFacts = []
          Path = [CallableAggregatePathStep.UnionPayload(0, 0)]; SourceType = callableType
          Contract = Result.Error "The absent Ok case has no formed callable family."
          Participants = [p ParticipantRole.AggregateSlot 0 (NodeId 99) (NodeId 99)] }
    let row : CallableAggregateValue =
        { Occurrence = initialization.Id; Aggregate = initialization.Id; Slot = slot.Identity
          Alternatives = []; Selector = None; FormationInputs = []; Value = None; SelectedAlternative = None
          Operation = CallableAggregateOperation.Construct; Frontier = None
          Tag = Some { Constructor = initialization.Id; TagRead = None; CaseOrdinal = 1
                       PayloadOrdinal = Some 0; Payload = Some payload.Id
                       Participants = [p ParticipantRole.AggregateConstructor 0 initialization.Id initialization.Id
                                       p ParticipantRole.AggregatePayload 0 initialization.Id payload.Id] }
          Bytes = 0; Alignment = 1; Participants = [] }
    let row = { row with Participants = valueParticipants row }
    let account : CallableAggregateDependencyAccount =
        { Occurrence = initialization.Id; Slots = [slot]; Values = [row]; Carriers = []; Contracts = []
          Flows = []; Joins = []; Participants = []; Sources = []; Claims = []; Symbols = []; Inactivity = [] }
    let held = [payload; initialization]
    let raw = revision held
    let absentComponent = ValueRepresentation.CallableComponent(slot.Identity, ValueRepresentation.Record([], Some([], 0, 1)))
    let represented =
        ValueRepresentation.Union(["Ok", [absentComponent]; "Error", [ValueRepresentation.Scalar SettledSlot.Bool]], Some(1, 2, 1))
    let graph =
        { raw with
            Codata = { raw.Codata with Escapes = Map.ofList [initialization.Id, EscapeKind.StackScoped] }
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
                            Layouts = Map.ofList [resultType, SettledLayout.Union(["Ok", Some(SettledSlot.InlineBytes(0, 1)); "Error", Some SettledSlot.Bool], Some 1, Some 2, Some 1)]
                            OccurrenceRepresentations =
                                Map.ofList [payload.Id, Ok(ValueRepresentation.Scalar SettledSlot.Bool)
                                            initialization.Id, Ok represented] } } }
        |> seal [] [1, [1]; 2, [1; 2]]
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode payload.Id (Arg 1) (TInt(IntWidth 1)) operands
    let output = observe true graph initialization operands
    let operations = output.InlineOps
    match output.Result with TRValue _ -> () | other -> failwithf "Absent callable case dropped its scalar payload: %A" other
    Assert.Contains(operations, function
        | MLIROp.MemRefOp(MemRefOp.StoreAligned(Arg 1, _, _, TInt(IntWidth 1), _, _)) -> true
        | _ -> false)
    Assert.DoesNotContain(operations, function MLIROp.FuncOp(FuncOp.FuncConstant _) -> true | _ -> false)
    Assert.Empty(graph.Emission.Callable.Contracts)
    Assert.Empty(operands.Errors)
