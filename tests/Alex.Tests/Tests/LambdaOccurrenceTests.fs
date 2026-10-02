module Alex.Tests.LambdaOccurrenceTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

// The rows below are what the compiler service publishes for the fixtures of this
// file. They were printed from the compiler service and copied here.

/// The target of the numeric domain relation. It is unreachable and no witness visits it.
let private numericDomain number =
    { node number (SemanticKind.Literal NativeLiteral.Unit) unitType [] None with IsReachable = false }

let private idsOf (held: SemanticNode list) = held |> List.map (fun held -> held.Id)

/// The carrier of a Boolean occurrence. The participants include the numeric domain node.
let private boolCarrier (site: SemanticNode) (participants: SemanticNode list) : ScalarCarrier =
    { Site = site.Id; Slot = SettledSlot.Bool; Range = ValueRange.Bounded(0I, 1I)
      Representation = None; Declaration = None; SourceType = boolType; Obligations = []
      Participants = Set.ofList (idsOf participants) }

let private boolForm : Result<ValueRepresentation, string> = Ok(ValueRepresentation.Scalar SettledSlot.Bool)
let private unitForm : Result<ValueRepresentation, string> = Ok(ValueRepresentation.Scalar SettledSlot.Unit)
let private callableForm : Result<ValueRepresentation, string> =
    Result.Error "Callable values require their separately published code and environment components."

/// The carrier of a callable occurrence whose code takes no environment.
let private codeCarrier (occurrence: SemanticNode) (implementation: SemanticNode)
                        (parameters: (string * TypeIdentity * NodeId) list) (body: SemanticNode) : CallableCarrier =
    { Occurrence = occurrence.Id; SourceType = occurrence.Type; Implementation = implementation.Id
      Parameters = parameters
      ParameterShapes = parameters |> List.map (fun (_, _, formal) -> CallableValueShape.Data formal)
      OmittedParameters = Set.empty
      Result = body.Id; ResultShape = CallableValueShape.Data body.Id
      Environment = None }

let private rowsOf (rows: ('key * 'row) list list) = rows |> List.concat |> Map.ofList

/// A settled component graph shares one environment read and formal across two
/// function occurrences. The second occurrence places that formal at argument 1;
/// the nodes' single Parent fields deliberately describe only the first use.
[<Fact>]
let ``shared body reads each lambda occurrence's block argument and restores outer operands`` () =
    let environmentType = arrayOf uint8Type
    let formal = node 0 (SemanticKind.PatternBinding "environment") environmentType [] (Some 9)
    let padding = node 1 (SemanticKind.PatternBinding "padding") boolType [] (Some 10)
    let capture = node 2 (SemanticKind.PatternBinding "captured") boolType [] None
    let externalValue = node 3 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let externalBinding = node 4 (SemanticKind.Binding("alreadyFormed", false, false, None)) boolType [3] None
    let externalRead = node 5 (SemanticKind.VarRef("alreadyFormed", Some externalBinding.Id)) boolType [] (Some 8)
    let environmentRead = node 6 (SemanticKind.VarRef("environment", Some formal.Id)) environmentType [] (Some 7)
    let read = node 7 (SemanticKind.EnvironmentRead(environmentRead.Id, capture.Id)) boolType [6] (Some 8)
    let body = node 8 (SemanticKind.Sequential [externalRead.Id; read.Id]) boolType [5; 7] (Some 9)
    let makeLambda number parameters children ty =
        node number (SemanticKind.Lambda(parameters, body.Id, [], None, LambdaContext.RegularClosure)) ty children (Some 11)
    let firstParameters = ["environment", environmentType, formal.Id]
    let secondParameters = ["padding", boolType, padding.Id; "environment", environmentType, formal.Id]
    let first = makeLambda 9 firstParameters [0; 8] (functionFrom environmentType boolType)
    let second = makeLambda 10 secondParameters [1; 0; 8] (functionFrom boolType first.Type)
    let root = node 11 (SemanticKind.Sequential [first.Id; second.Id]) unitType [9; 10] None
    let slot: ContinuationSlot =
        { Source = capture.Id; ValueType = boolType; IsCapture = true
          Holds = CaptureSlotKind.Scalar SettledSlot.Bool
          Field = { Name = "captured"; Slot = SettledSlot.Bool; Offset = Some 0; Size = Some 1; Align = Some 1 } }
    let obligation =
        { Id = "shared_environment_layout"; Kind = "continuation-layout"; Logic = "QF_LIA"
          Statement = "The supplied bool field occupies its one-byte environment"
          Source = "Alex component fixture"; Refs = []
          Body = ObligationBody.ContinuationLayout([0, 1, 1], 1, 1) }
    let proof = node 12 (SemanticKind.Obligation obligation) unitType [] None
    let layout: EnvironmentLayout =
        { Owner = first.Id; Implementation = first.Id; Formal = formal.Id
          Slots = [slot]; Bytes = 1; Alignment = 1; Obligations = [proof.Id] }
    let domain = numericDomain 13
    let data = [formal; padding; capture; externalValue; externalBinding; externalRead; environmentRead; read; body; root; proof]
    let carriers =
        Map.ofList [ first.Id, codeCarrier first first firstParameters body
                     second.Id, codeCarrier second second secondParameters body ]
    let declaration (lambda: SemanticNode) parameters participants : CallableEmissionDeclaration =
        { Lookup = lambda.Id; Implementation = lambda.Id; Parameters = parameters; Result = body.Id
          Context = LambdaContext.RegularClosure; Captures = []
          Name = CallableSymbolName.Anonymous lambda.Id; Parent = Some root.Id
          Participants = Set.ofList (idsOf participants) }
    let buffer : Result<ValueRepresentation, string> =
        Ok(ValueRepresentation.Buffer(Some 1, ValueRepresentation.Scalar(SettledSlot.Integer(8, None))))
    let byte = SettledSlot.Integer(8, Some "uint8")
    let callable : CallableEmissionProjection =
        { Empty.callable with
            Carriers = carriers
            ValueShapes =
                rowsOf [ data |> List.map (fun held -> held.Id, CallableValueShape.Data held.Id)
                         [first; second] |> List.map (fun held -> held.Id, CallableValueShape.Callable held.Id) ]
            SignatureData = Map.ofList [first.Id, Set.empty; second.Id, Set.empty]
            Transports = Map.ofList [first.Id, Set.singleton first.Id; second.Id, Set.singleton second.Id]
            Declarations =
                Map.ofList [ first.Id, declaration first firstParameters [formal; body; first; root]
                             second.Id, declaration second secondParameters [formal; padding; body; second; root] ]
            Symbols =
                Map.ofList [ externalBinding.Id, CallableSymbolName.RootBinding "alreadyFormed"
                             first.Id, CallableSymbolName.Anonymous first.Id
                             second.Id, CallableSymbolName.Anonymous second.Id ]
            Arguments =
                Map.ofList [ first.Id, Map.ofList [formal.Id, [0]]
                             second.Id, Map.ofList [formal.Id, [1]; padding.Id, [0]] ]
            AliasTargets =
                rowsOf [ [formal; padding; capture; externalValue; read; body; first; second; root; proof]
                         |> List.map (fun held -> held.Id, held.Id)
                         [ externalBinding.Id, externalValue.Id
                           externalRead.Id, externalValue.Id
                           environmentRead.Id, formal.Id ] ]
            UnitNodes = Set.ofList [root.Id; proof.Id]
            ClosedData = Set.ofList (idsOf data)
            Supports =
                rowsOf [ [formal; padding; capture; externalValue; read; body; root; proof]
                         |> List.map (fun held -> held.Id, Set.singleton held.Id)
                         [ externalBinding.Id, Set.ofList (idsOf [externalValue; externalBinding])
                           externalRead.Id, Set.ofList (idsOf [externalValue; externalBinding; externalRead])
                           environmentRead.Id, Set.ofList (idsOf [formal; environmentRead])
                           first.Id, Set.ofList (idsOf [formal; body; first; root])
                           second.Id, Set.ofList (idsOf [formal; padding; body; second; root]) ] ] }
    let values =
        [ boolCarrier padding [padding; domain]
          boolCarrier capture [capture; domain]
          boolCarrier externalValue [externalValue; domain]
          boolCarrier externalBinding [externalBinding; domain]
          boolCarrier externalRead [externalBinding; externalRead; domain]
          boolCarrier read [capture; environmentRead; read; domain]
          boolCarrier body [externalRead; read; body; domain] ]
    let numeric : NumericWitnessProjection =
        { Empty.numeric with
            Values = values |> List.map (fun held -> held.Site, held) |> Map.ofList
            Required = values |> List.map (fun held -> held.Site) |> Set.ofList
            ResultSites = Set.ofList (idsOf [externalValue; externalRead; read; body])
            SourceTypes = data @ [first; second] |> List.map (fun held -> held.Id, held.Type) |> Map.ofList
            DeclaredScalars = Map.ofList [NTUKind.NTUuint(NTUWidth.Fixed 8), byte]
            OccurrenceRepresentations =
                rowsOf [ [formal; environmentRead] |> List.map (fun held -> held.Id, buffer)
                         [padding; capture; externalValue; externalBinding; externalRead; read; body]
                         |> List.map (fun held -> held.Id, boolForm)
                         [first; second] |> List.map (fun held -> held.Id, callableForm)
                         [root; proof] |> List.map (fun held -> held.Id, unitForm) ]
            TypeRepresentations =
                Map.ofList [ environmentType, Ok(ValueRepresentation.Buffer(None, ValueRepresentation.Scalar byte))
                             boolType, boolForm
                             unitType, unitForm
                             uint8Type, Ok(ValueRepresentation.Scalar byte)
                             first.Type, callableForm
                             second.Type, callableForm ] }
    let graph =
        { revision (data @ [first; second; domain]) with
            Codata =
                { Codata.empty with
                    EnvironmentLayouts = Map.ofList [first.Id, layout]
                    EnvironmentOrigins = Map.ofList [formal.Id, first.Id; environmentRead.Id, first.Id]
                    CallableCarriers = carriers }
            Emission = { Empty.emission with Callable = callable; Numeric = numeric }
            Obligations = [obligation] }
    let graph = declareBindingReadings graph
    let operands = MLIRAccumulator.empty ()
    let carrier = TMemRefStatic(1, TInt(IntWidth 8))
    MLIRAccumulator.bindNode formal.Id (V(-20, 0)) carrier operands
    MLIRAccumulator.bindNode externalBinding.Id (V(-21, 0)) (TInt(IntWidth 1)) operands
    let parentAssociations, parentTypes = operands.NodeAssoc, operands.SSATypes
    let rootScope = ref (ScopeContext.root ())
    let visited = ref (Set.ofList [externalBinding.Id; externalValue.Id])
    let position = Zipper.create graph root.Id |> require "Missing shared-body root"
    let context =
        { Coeffects = coeffects 64; Accumulator = operands; RootAccumulator = operands
          ScopeContext = rootScope; RootScopeContext = rootScope; Graph = graph; Zipper = position
          GlobalVisited = visited; TraversalVisited = visited }
    let readOccurrences = ResizeArray<NodeId>()
    let rec witness ctx (node: SemanticNode) =
        if node.Id = read.Id then
            readOccurrences.Add((Zipper.findEnclosingLambda ctx.Zipper |> require "Read lost its actual lambda occurrence").Id)
        Assert.NotEqual(externalBinding.Id, node.Id)
        Assert.NotEqual(externalValue.Id, node.Id)
        match node.Kind with
        | SemanticKind.Lambda _ ->
            (Alex.Witnesses.LambdaWitness.createNanopass (fun () -> witness)).Witness ctx node
        | SemanticKind.VarRef _ -> Alex.Witnesses.VarRefWitness.nanopass.Witness ctx node
        | SemanticKind.EnvironmentRead _ -> Alex.Witnesses.EnvironmentWitness.nanopass.Witness ctx node
        | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    visitAllNodes witness context position.Focus visited
    Assert.Empty operands.Errors
    Assert.Equal<NodeId list>([first.Id; second.Id], List.ofSeq readOccurrences)
    Assert.Same(parentAssociations, operands.NodeAssoc)
    Assert.Same(parentTypes, operands.SSATypes)
    let operations = ScopeContext.getOps rootScope.Value
    let definitions =
        operations |> List.choose (function
            | MLIROp.FuncOp(FuncOp.FuncDef(name, parameters, returnType, body, _)) -> Some(name, parameters, returnType, body)
            | _ -> None)
    Assert.Equal(2, definitions.Length)
    for fn, argument in [first, Arg 0; second, Arg 1] do
        let name = Alex.CodeGeneration.CallableSymbols.lambda graph graph.Nodes[fn.Id] false
        let _, parameters, returnTypes, emitted = definitions |> List.find (fun (actual, _, _, _) -> actual = name)
        let returnType = Assert.Single returnTypes
        Assert.Contains((argument, carrier), parameters)
        Assert.Equal(TInt(IntWidth 1), returnType)
        let views = emitted |> List.choose (function
            | MLIROp.MemRefOp(MemRefOp.View(_, source, _, sourceType, _)) -> Some(source, sourceType)
            | _ -> None)
        Assert.Equal((argument, carrier), Assert.Single views)
        let loaded = emitted |> List.choose (function
            | MLIROp.MemRefOp(MemRefOp.LoadAligned(result, _, _, _, _, _)) -> Some result
            | _ -> None) |> Assert.Single
        Assert.Contains(MLIROp.FuncOp(FuncOp.Return([{ SSA = loaded; Type = returnType }])), emitted)
    // Verify the actual witness output, including per-function definitions and
    // block argument uses. This is a component gate, not a source/native oracle.
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "lambda_occurrences" operations
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.DoesNotContain("unrealized_conversion_cast", verified)

/// One function of the dependency fixture with the nodes it owns. A call names the
/// reference, the application and the function called.
type private Function =
    { Name: string
      Formal: SemanticNode
      Read: SemanticNode
      Calls: (SemanticNode * SemanticNode * Function) list
      Body: SemanticNode
      Lambda: SemanticNode
      Binding: SemanticNode }

let private functionType = functionFrom boolType boolType

/// The nodes of one function, numbered from `first` in the order of their creation at
/// the notch: the formal, its read, a reference and a call for each dependency, the
/// body, the lambda and the binding.
let private makeFunction first name (dependencies: Function list) : Function =
    let bodyNumber = first + 2 + 2 * List.length dependencies
    let lambdaNumber, bindingNumber = bodyNumber + 1, bodyNumber + 2
    let formal = node first (SemanticKind.PatternBinding "value") boolType [] (Some lambdaNumber)
    let read = node (first + 1) (SemanticKind.VarRef("value", Some formal.Id)) boolType [] (Some bodyNumber)
    let calls =
        dependencies |> List.mapi (fun index dependency ->
            let referenceNumber, callNumber = first + 2 + 2 * index, first + 3 + 2 * index
            let reference =
                node referenceNumber (SemanticKind.VarRef("dependency", Some dependency.Binding.Id)) functionType [] (Some callNumber)
            let call =
                node callNumber (SemanticKind.Application(reference.Id, [read.Id])) boolType
                    [referenceNumber; first + 1] (Some bodyNumber)
            reference, call, dependency)
    let elements = (calls |> List.map (fun (_, call, _) -> call)) @ [read]
    let body =
        node bodyNumber (SemanticKind.Sequential (idsOf elements)) boolType
            (elements |> List.map (fun held -> NodeId.value held.Id)) (Some lambdaNumber)
    let lambda =
        node lambdaNumber
            (SemanticKind.Lambda(["value", boolType, formal.Id], body.Id, [], None, LambdaContext.RegularClosure))
            functionType [first; bodyNumber] (Some bindingNumber)
    let binding = node bindingNumber (SemanticKind.Binding(name, false, false, None)) functionType [lambdaNumber] None
    { Name = name; Formal = formal; Read = read; Calls = calls; Body = body; Lambda = lambda; Binding = binding }

let private parametersOf (owner: Function) = ["value", boolType, owner.Formal.Id]
let private referencesOf (owner: Function) = owner.Calls |> List.map (fun (reference, _, _) -> reference)
let private callsOf (owner: Function) = owner.Calls |> List.map (fun (_, call, _) -> call)
let private dataOf (owner: Function) = [owner.Formal; owner.Read] @ callsOf owner @ [owner.Body]
let private callablesOf (owner: Function) = referencesOf owner @ [owner.Lambda; owner.Binding]
let private nodesOf (owner: Function) =
    [owner.Formal; owner.Read]
    @ (owner.Calls |> List.collect (fun (reference, call, _) -> [reference; call]))
    @ [owner.Body; owner.Lambda; owner.Binding]

/// What the compiler service publishes for the functions of the dependency fixture.
let private published (functions: Function list) (domain: SemanticNode) : Revision =
    let each (rows: Function -> ('key * 'row) list) = functions |> List.collect rows |> Map.ofList
    let members (rows: Function -> SemanticNode list) = functions |> List.collect rows |> idsOf |> Set.ofList
    let carriers =
        each (fun owner ->
            [owner.Lambda; owner.Binding]
            |> List.map (fun held -> held.Id, codeCarrier held owner.Lambda (parametersOf owner) owner.Body)
            |> List.append (owner.Calls |> List.map (fun (reference, _, callee) ->
                reference.Id, codeCarrier reference callee.Lambda (parametersOf callee) callee.Body)))
    let declaration (owner: Function) (lookup: SemanticNode) parent : CallableEmissionDeclaration =
        { Lookup = lookup.Id; Implementation = owner.Lambda.Id; Parameters = parametersOf owner; Result = owner.Body.Id
          Context = LambdaContext.RegularClosure; Captures = []
          Name = CallableSymbolName.RootBinding owner.Name; Parent = parent
          Participants = Set.ofList (idsOf [owner.Formal; owner.Body; owner.Lambda; owner.Binding]) }
    let callable : CallableEmissionProjection =
        { Empty.callable with
            Carriers = carriers
            ValueShapes =
                each (fun owner ->
                    (dataOf owner |> List.map (fun held -> held.Id, CallableValueShape.Data held.Id))
                    @ (callablesOf owner |> List.map (fun held -> held.Id, CallableValueShape.Callable held.Id)))
            SignatureData = each (fun owner -> [owner.Lambda.Id, Set.empty])
            Calls =
                each (fun owner ->
                    owner.Calls |> List.map (fun (reference, call, callee) ->
                        call.Id,
                        { Site = call.Id; Implementation = callee.Lambda.Id; Parameters = parametersOf callee
                          Arguments = [owner.Read.Id]; Result = callee.Body.Id; SignatureData = Set.empty
                          Participants =
                            Set.ofList (idsOf [callee.Formal; callee.Body; callee.Lambda; owner.Read; reference; call]) }))
            Transports =
                each (fun owner ->
                    [ owner.Lambda.Id, Set.singleton owner.Lambda.Id
                      owner.Binding.Id, Set.ofList (idsOf [owner.Lambda; owner.Binding]) ]
                    @ (owner.Calls |> List.map (fun (reference, _, callee) ->
                        reference.Id, Set.ofList (idsOf [callee.Lambda; callee.Binding; reference]))))
            Declarations =
                each (fun owner ->
                    [ owner.Lambda.Id, declaration owner owner.Lambda (Some owner.Binding.Id)
                      owner.Binding.Id, declaration owner owner.Binding None ])
            Symbols =
                each (fun owner ->
                    [owner.Lambda; owner.Binding]
                    |> List.map (fun held -> held.Id, CallableSymbolName.RootBinding owner.Name))
            DirectCallees =
                each (fun owner -> owner.Calls |> List.map (fun (reference, _, callee) -> reference.Id, callee.Binding.Id))
            FunctionBindings = members (fun owner -> [owner.Binding])
            DefinitionOnlyBindings = members (fun owner -> [owner.Binding])
            DefinitionOnlyLambdas = members (fun owner -> [owner.Lambda])
            Arguments = each (fun owner -> [owner.Lambda.Id, Map.ofList [owner.Formal.Id, [0]]])
            AliasTargets =
                each (fun owner ->
                    [ owner.Formal.Id, owner.Formal.Id
                      owner.Read.Id, owner.Formal.Id
                      owner.Body.Id, owner.Body.Id
                      owner.Lambda.Id, owner.Lambda.Id
                      owner.Binding.Id, owner.Lambda.Id ]
                    @ (owner.Calls |> List.collect (fun (reference, call, callee) ->
                        [reference.Id, callee.Lambda.Id; call.Id, call.Id])))
            ClosedData = members dataOf
            Supports =
                each (fun owner ->
                    let declared = Set.ofList (idsOf [owner.Formal; owner.Body; owner.Lambda; owner.Binding])
                    [ owner.Formal.Id, Set.singleton owner.Formal.Id
                      owner.Read.Id, Set.ofList (idsOf [owner.Formal; owner.Read])
                      owner.Body.Id, Set.singleton owner.Body.Id
                      owner.Lambda.Id, declared
                      owner.Binding.Id, declared ]
                    @ (owner.Calls |> List.collect (fun (reference, call, callee) ->
                        [ reference.Id, Set.ofList (idsOf [callee.Lambda; callee.Binding; reference])
                          call.Id, Set.ofList (idsOf [callee.Formal; callee.Body; callee.Lambda; owner.Read; reference; call]) ]))) }
    let values =
        functions |> List.collect (fun owner ->
            [ boolCarrier owner.Formal [owner.Formal; domain]
              boolCarrier owner.Read [owner.Formal; owner.Read; domain] ]
            @ (owner.Calls |> List.map (fun (reference, call, _) -> boolCarrier call [owner.Read; reference; call; domain]))
            @ [ boolCarrier owner.Body (callsOf owner @ [owner.Read; owner.Body; domain]) ])
    let numeric : NumericWitnessProjection =
        { Empty.numeric with
            Values = values |> List.map (fun held -> held.Site, held) |> Map.ofList
            Required = values |> List.map (fun held -> held.Site) |> Set.ofList
            ResultSites = members (fun owner -> [owner.Read] @ callsOf owner @ [owner.Body])
            SourceTypes = each (fun owner -> nodesOf owner |> List.map (fun held -> held.Id, held.Type))
            OccurrenceRepresentations =
                each (fun owner ->
                    (dataOf owner |> List.map (fun held -> held.Id, boolForm))
                    @ (callablesOf owner |> List.map (fun held -> held.Id, callableForm)))
            TypeRepresentations = Map.ofList [boolType, boolForm; functionType, callableForm] }
    { revision ((functions |> List.collect nodesOf) @ [domain]) with
        Codata = { Codata.empty with CallableCarriers = carriers }
        Emission = { Empty.emission with Callable = callable; Numeric = numeric } }
    |> declareBindingReadings

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``definition discovered inside a dependency is reused by later reference and structural occurrences`` (structuralOccurrence: bool) =
    let dependencyFunction = makeFunction 0 "dependency" []
    let middleFunction = makeFunction 5 "middle" [dependencyFunction]
    let callerFunction = makeFunction 12 "caller" [middleFunction; dependencyFunction]
    let dependencyLambda = dependencyFunction.Lambda
    let caller, callerLambda = callerFunction.Binding, callerFunction.Lambda
    let domain = numericDomain 21
    let raw = published [dependencyFunction; middleFunction; callerFunction] domain
    let graph =
        if structuralOccurrence then
            let bodyId =
                match callerLambda.Kind with
                | SemanticKind.Lambda (_, body, _, _, _) -> body
                | _ -> failwith "Fixture caller is not a lambda"
            let body = raw.Nodes[bodyId]
            let children = body.Children.Head :: dependencyLambda.Id :: body.Children.Tail
            // Materialized ClosureValue nodes and the implementation's named
            // binding both structurally reference the same code Lambda. Its
            // canonical parent still identifies the one code declaration.
            let updated = { body with Kind = SemanticKind.Sequential children; Children = children }
            // The carrier of the body names every child of the body as a participant.
            let carrier = raw.Emission.Numeric.Values[bodyId]
            let participants = { carrier with Participants = Set.add dependencyLambda.Id carrier.Participants }
            { raw with
                Nodes = Map.add bodyId updated raw.Nodes
                Emission =
                    { raw.Emission with
                        Numeric = { raw.Emission.Numeric with Values = Map.add bodyId participants raw.Emission.Numeric.Values } } }
            |> declareTraversalReadings
        else raw
    let operands = MLIRAccumulator.empty ()
    let rootScope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    let position = Zipper.create graph caller.Id |> require "Missing dependency caller"
    let context =
        { Coeffects = coeffects 64; Accumulator = operands; RootAccumulator = operands
          ScopeContext = rootScope; RootScopeContext = rootScope; Graph = graph; Zipper = position
          GlobalVisited = visited; TraversalVisited = visited }
    let dependencyVisits = ResizeArray<NodeId>()
    let rec witness ctx (node: SemanticNode) =
        if node.Id = dependencyLambda.Id then dependencyVisits.Add node.Id
        match node.Kind with
        | SemanticKind.Lambda _ -> (Alex.Witnesses.LambdaWitness.createNanopass (fun () -> witness)).Witness ctx node
        | SemanticKind.VarRef _ -> Alex.Witnesses.VarRefWitness.nanopass.Witness ctx node
        | SemanticKind.Binding _ -> Alex.Witnesses.BindingWitness.nanopass.Witness ctx node
        | SemanticKind.Application _ -> Alex.Witnesses.ApplicationWitness.nanopass.Witness ctx node
        | _ -> Alex.Witnesses.StructuralWitness.nanopass.Witness ctx node
    // A reference never places its binding. Each definition is witnessed from its own
    // declaration, and the declarations are visited in their order, as the entry visits
    // the definitions of a module. The visited set and the scopes are shared.
    for declaration in [dependencyFunction.Binding; middleFunction.Binding; callerFunction.Binding] do
        let start = Zipper.create graph declaration.Id |> require "Missing declaration"
        visitAllNodes witness { context with Zipper = start } start.Focus visited
    Assert.Same(position.Graph, graph)
    Assert.Empty operands.Errors
    Assert.Equal(dependencyLambda.Id, Assert.Single dependencyVisits)
    let operations = ScopeContext.getOps rootScope.Value
    let definitions = operations |> List.choose (function
        | MLIROp.FuncOp(FuncOp.FuncDef(name, _, _, _, _)) -> Some name
        | _ -> None)
    Assert.Equal(3, definitions.Length)
    Assert.Equal(3, definitions |> Set.ofList |> Set.count)
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "dependency_reuse" operations
    Alex.Tests.Tools.mlirOpt ["--verify-each"] text |> ignore

[<Fact>]
let ``occurrence-bound formal read emits its settled refinement before consumption`` () =
    let formal = node 0 (SemanticKind.PatternBinding "value") intType [] None
    let read = node 1 (SemanticKind.VarRef("value", Some formal.Id)) intType [] None
    // The component receives the already settled read meet. It must retain the
    // actual occurrence's argument SSA while emitting that physical conversion.
    let meet = { Consumer = read.Id; Operand = read.Id; From = 64; To = 8; Adapt = MeetKind.Truncate }
    // The compiler service refuses this fixture: it settles no carrier for an integer
    // that has no analysed range. The Callable rows have the form it publishes for a
    // formal and its read. No Numeric row is stated.
    let graph =
        { revision [formal; read] with
            Codata = { Codata.empty with Meets = Map.ofList [read.Id, [meet]] }
            Emission =
                { Empty.emission with
                    Callable =
                        { Empty.callable with
                            ValueShapes = [formal; read] |> List.map (fun held -> held.Id, CallableValueShape.Data held.Id) |> Map.ofList
                            AliasTargets = Map.ofList [formal.Id, formal.Id; read.Id, formal.Id]
                            ClosedData = Set.ofList (idsOf [formal; read])
                            Supports =
                                Map.ofList [ formal.Id, Set.singleton formal.Id
                                             read.Id, Set.ofList (idsOf [formal; read]) ] } } }
    let graph = declareBindingReadings graph
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode formal.Id (Arg 1) (TInt(IntWidth 64)) operands
    let position = Zipper.create graph read.Id |> require "Missing refined formal read"
    let scope = ref (ScopeContext.root ())
    let visited = ref (Set.singleton formal.Id)
    let context =
        { Coeffects = coeffects 64; Accumulator = operands; RootAccumulator = operands
          ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
          GlobalVisited = visited; TraversalVisited = visited }
    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness context position.Focus
    match output.Result with
    | TRValue value ->
        Assert.Equal(TInt(IntWidth 8), value.Type)
        Assert.Equal(MLIROp.ArithOp(ArithOp.TruncI(value.SSA, Arg 1, TInt(IntWidth 64), TInt(IntWidth 8))),
                     Assert.Single output.InlineOps)
        let body = output.InlineOps @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = value.SSA; Type = value.Type }]))]
        let definition = MLIROp.FuncOp(FuncOp.FuncDef("refined_read",
            [Arg 0, TInt(IntWidth 1); Arg 1, TInt(IntWidth 64)], [value.Type], body, FuncVisibility.Public))
        let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "refined_formal" [definition]
        Alex.Tests.Tools.mlirOpt ["--verify-each"] text |> ignore
    | other -> failwithf "No value from refined formal read: %A" other
