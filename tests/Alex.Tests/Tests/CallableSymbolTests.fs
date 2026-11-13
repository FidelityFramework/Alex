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

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``checked text cannot acquire portable text without its selected validator and retirement realization`` retirement =
  let snapshot = { SSA = Arg 0; Type = TMemRef(TInt(IntWidth 8)) }
  let result = { SSA = V(2, 0); Type = TInt(IntWidth 8) }
  let operation =
    if retirement then Utf8SnapshotRetire(NodeId 2, snapshot)
    else Utf8Validate(NodeId 2, snapshot, result)
  Assert.Equal(NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [operation])
  let error = Assert.ThrowsAny<System.Exception>(fun () ->
    Alex.Dialects.Core.Serialize.opToString (Ok 64) operation |> ignore)
  Assert.Contains("exact snapshot, validator and retirement accounts", error.Message)
  Assert.Equal<MLIROp list>([operation], OperationStructure.flatten [operation])

[<Fact>]
let ``Pending obligation emits no solver operation or placeholder and retains ready text`` () =
  let ready: ObligationInfo =
    { Id = "ready_transfer"; Kind = "component-transfer"; Logic = "QF_LIA"
      Statement = "Ready component"; Source = "pending-transfer:1"; Refs = []
      Body = ObligationBody.IntegerRepresentationCoverage(0I, 0I, -128I, 127I) }
  let pending =
    { ready with Id = "pending_transfer"; Logic = ""
                 Body = ObligationBody.Pending ["Selected target conversion remains Pending."] }
  Assert.Empty(Alex.Traversal.SMTTransfer.operations [pending])
  let ordinary = Alex.Traversal.SMTTransfer.transfer [ready]
  let mixed = Alex.Traversal.SMTTransfer.transfer [pending; ready; pending]
  Assert.Equal(ordinary, mixed)
  Assert.Contains("ready_transfer", mixed)
  Assert.DoesNotContain("pending_transfer", mixed)

[<Fact>]
let ``optional Some call intent requires selected target realization and retains explicit slots`` () =
  let original = { SSA = Arg 0; Type = TMemRefStatic(1, TInt(IntWidth 8)) }
  let code = { SSA = Arg 1; Type = TFunc([], []) }
  let slot = { Ordinal = 0; Choice = OptionalEntrySlotChoice.Direct { CaseOrdinal = 1; Claim = NodeId 3; Code = Some code } }
  let operation = OptionalEntryCall(NodeId 2, [original], [slot], [])
  Assert.Equal(NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [operation])
  let error = Assert.ThrowsAny<System.Exception>(fun () ->
    Alex.Dialects.Core.Serialize.opToString (Ok 64) operation |> ignore)
  Assert.Contains("exact source conversion accounts", error.Message)
  match OperationStructure.flatten [operation] with
  | [OptionalEntryCall(site, arguments, [actual], results)] ->
    Assert.Equal(NodeId 2, site)
    Assert.Equal<Val list>([original], arguments)
    Assert.Equal(0, actual.Ordinal)
    match actual.Choice with
    | OptionalEntrySlotChoice.Direct arm ->
      Assert.Equal(1, arm.CaseOrdinal)
      Assert.Equal(NodeId 3, arm.Claim)
      Assert.Equal(Some code, arm.Code)
    | other -> failwithf "Expected direct optional slot choice: %A" other
    Assert.Empty results
  | other -> failwithf "Optional conversion lost its explicit source incidence: %A" other

[<Fact>]
let ``optional None call intent retains the original Option without a code value`` () =
  let original = { SSA = Arg 0; Type = TMemRefStatic(1, TInt(IntWidth 8)) }
  let slot = { Ordinal = 0; Choice = OptionalEntrySlotChoice.Direct { CaseOrdinal = 0; Claim = NodeId 3; Code = None } }
  let operation = OptionalEntryCall(NodeId 2, [original], [slot], [])
  Assert.Equal(NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [operation])
  match OperationStructure.flatten [operation] with
  | [OptionalEntryCall(_, [actual], [slot], [])] ->
    Assert.Equal(original, actual)
    match slot.Choice with
    | OptionalEntrySlotChoice.Direct arm ->
      Assert.Equal(0, arm.CaseOrdinal)
      Assert.True(arm.Code.IsNone)
    | other -> failwithf "Expected direct optional absence choice: %A" other
  | other -> failwithf "None lost its original optional intent: %A" other

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``conditional optional call intent requires target realization and preserves forward and reversed arm order`` reversed =
  let original = { SSA = Arg 0; Type = TMemRefStatic(1, TInt(IntWidth 8)) }
  let tag = { SSA = V(5, 0); Type = TInt(IntWidth 64) }
  let code = { SSA = Arg 1; Type = TFunc([], []) }
  let presentArm = { CaseOrdinal = 1; Claim = NodeId 3; Code = Some code }
  let absentArm = { CaseOrdinal = 0; Claim = NodeId 4; Code = None }
  let whenTrue, whenFalse = if reversed then absentArm, presentArm else presentArm, absentArm
  let slot = { Ordinal = 0; Choice = OptionalEntrySlotChoice.Conditional(NodeId 6, tag, whenTrue, whenFalse) }
  let operation = OptionalEntryCall(NodeId 2, [original], [slot], [])
  Assert.Equal(NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [operation])
  let error = Assert.ThrowsAny<System.Exception>(fun () ->
    Alex.Dialects.Core.Serialize.opToString (Ok 64) operation |> ignore)
  Assert.Contains("exact source conversion accounts", error.Message)
  match OperationStructure.flatten [operation] with
  | [OptionalEntryCall(site, [actual], [held], [])] ->
    Assert.Equal(NodeId 2, site)
    Assert.Equal(original, actual)
    Assert.Equal(0, held.Ordinal)
    match held.Choice with
    | OptionalEntrySlotChoice.Conditional(selection, heldTag, heldTrue, heldFalse) ->
      Assert.Equal(NodeId 6, selection)
      Assert.Equal(tag, heldTag)
      Assert.Equal(whenTrue, heldTrue)
      Assert.Equal(whenFalse, heldFalse)
    | other -> failwithf "Expected conditional optional slot choice: %A" other
  | other -> failwithf "Conditional optional intent lost its explicit source incidence: %A" other

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
      Kind = CallableKind.OrdinaryFlatClosure; Formation = NodeId(b + 2)
      EnvironmentValue = None; Contract = Ok(NodeId(b + 2)); Lifetime = []
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

let private context (graph: Revision) site (operands: MLIRAccumulator) =
    operands.WitnessScope <- Some (Alex.Correspondence.beginWholeGraphWitness graph)
    let rootScope = ref (ScopeContext.root ())
    let scope = ref (ScopeContext.createChild rootScope.Value FunctionLevel)
    let visited = ref Set.empty
    { Coeffects = coeffects 64
      Accumulator = operands; RootAccumulator = operands
      ScopeContext = scope; RootScopeContext = rootScope
      Graph = graph; Zipper = Zipper.create graph site |> require "Missing component site"
      GlobalVisited = visited; TraversalVisited = visited }

/// Component readings only: these stored rows select a physical native code
/// value. Source admission and full revision integrity are checked upstream.
let private closedReceivingFixture () =
    let graph, functions = fixture false
    let fn = functions.Head
    let symbol = lambda graph graph.Nodes[fn.Lambda] false
    let scalar = BoundaryScalar.Integer(64, true)
    let invocation : BoundaryCallbackInvocation =
        { Identity = NodeId 40; Import = NodeId 41; Parameter = 0; Formal = NodeId 42; Scope = NodeId 43
          Extent = BoundaryCallbackExtent.DuringCall
          Signature = {Parameters = [scalar]; Result = Some scalar; CallingConvention = "CDecl"}
          Contract = {Binding = "Foreign.call"; Parameter = 0
                      Signature = {Parameters = [|{Name = "value"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed,64); PassBy = BAREWire.Descriptors.PassBy.Value}|]
                                   ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed,64); CallingConvention = BAREWire.Descriptors.CallConv.CDecl}
                      Hypothesis = {Identity = "callback-demand"; Version = "1"; Source = "explicit-test-assumption"}; Scope = "Foreign.scope"}
          Participants = Set.ofList [NodeId 40; NodeId 41; NodeId 42; NodeId 43] }
    let entry : BoundaryClosedEntry =
        { Formation = fn.Call; Operand = fn.Reference; Declaration = fn.Binding; Implementation = fn.Lambda
          Formals = [NodeId 0]; Body = NodeId 1
          Lifetime = {Module = NodeId 7; Binding = fn.Binding; Implementation = fn.Lambda}
          Invocation = invocation.Identity; ParameterAdaptations = [None]; ResultAdaptation = None
          Registrations = Map.empty
          Transport = Set.ofList [fn.Call; fn.Reference]; Participants = Set.empty }
    let graph =
        {graph with
            Codata = {graph.Codata with FunctionPointers = Map.ofList [fn.Call, FunctionPointerPlan.Address(symbol,fn.Lambda)]}
            Emission = {graph.Emission with
                            Callable = {graph.Emission.Callable with NativeEntries = Map.ofList [fn.Lambda,symbol]}
                            Boundary = {graph.Emission.Boundary with CallbackInvocations = Map.ofList [invocation.Identity,invocation]; ClosedEntries = Map.ofList [entry.Formation,entry]}}}
    graph, fn, symbol

[<Fact>]
let ``closed receiving entry emits its full native function type without index repair`` () =
    let graph, fn, symbol = closedReceivingFixture ()
    let ctx = context graph fn.Call (MLIRAccumulator.empty ())
    let output = Alex.Witnesses.FunctionPointerWitness.nanopass.Witness ctx graph.Nodes[fn.Call]
    let expected = TFunc([TInt(IntWidth 64)], [TInt(IntWidth 64)])
    match output.Result, output.InlineOps with
    | TRValue value, [MLIROp.FuncOp(FuncOp.FuncConstant(ssa,actual,ty))] ->
        Assert.Equal(expected,value.Type)
        Assert.Equal(expected,ty)
        Assert.Equal(value.SSA,ssa)
        Assert.Equal(symbol,actual)
    | other -> failwithf "Closed native entry did not retain its exact signature: %A" other

[<Theory>]
[<InlineData("invocation", "exact invocation signature and complete declaration")>]
[<InlineData("formal", "exact invocation signature and complete declaration")>]
[<InlineData("unused", "omitted an original native formal")>]
[<InlineData("lifetime", "original ProgramImage code lifetime and symbol")>]
let ``closed receiving entry refuses missing or changed original account`` change reason =
    let graph, fn, _ = closedReceivingFixture ()
    let boundary = graph.Emission.Boundary
    let entry = boundary.ClosedEntries[fn.Call]
    let boundary =
        match change with
        | "invocation" -> {boundary with CallbackInvocations = Map.empty}
        | "formal" -> {boundary with ClosedEntries = Map.ofList [fn.Call,{entry with Formals = []}]}
        | "unused" ->
            let invocation = boundary.CallbackInvocations[entry.Invocation]
            {boundary with CallbackInvocations = Map.ofList [entry.Invocation,{invocation with Signature = {invocation.Signature with Parameters = []}}]}
        | _ -> {boundary with ClosedEntries = Map.ofList [fn.Call,{entry with Lifetime = {entry.Lifetime with Implementation = NodeId 999}}]}
    let graph = {graph with Emission = {graph.Emission with Boundary = boundary}}
    let ctx = context graph fn.Call (MLIRAccumulator.empty ())
    match (Alex.Witnesses.FunctionPointerWitness.nanopass.Witness ctx graph.Nodes[fn.Call]).Result with
    | TRError diagnostic -> Assert.Contains(reason,diagnostic.Message)
    | other -> failwithf "Malformed closed native entry was emitted: %A" other

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

/// Component contract for a local immutable imported code value. The declaration
/// is a leaf; only its admitted formation produces a function SSA value.
let private importedFixture () =
    let ty = functionFrom unitType unitType

    let nodes =
        [
            node 30 (SemanticKind.PatternBinding "externLeaf") ty [] (Some 31)
            node 31 (SemanticKind.Application(NodeId 30, [ NodeId 30 ])) ty [ 30 ] (Some 32)
            node 32 (SemanticKind.Binding("entry", false, false, None)) ty [ 31 ] (Some 35)
            node 33 (SemanticKind.VarRef("entry", Some(NodeId 32))) ty [] (Some 34)
            node 34 (SemanticKind.Application(NodeId 30, [ NodeId 33 ])) unitType [ 33 ] (Some 35)
            node 35 (SemanticKind.Sequential [ NodeId 32; NodeId 34 ]) unitType [ 32; 34 ] None
        ]

    let contract: BAREWire.Platform.ProcessLinkContract =
        {
            Identity = "fixture-process-link"
            Version = "1"
            Source = "fixture-explicit-assumption"
            Library = "c"
            Runtime = "libc"
            Os = "linux"
            Arch = "x86_64"
            LoadAt = "ProcessStartup"
            LiveUntil = "ProcessTermination"
            Unloading = "Forbidden"
            ExportedLibrary = "Forbidden"
        }

    let loading: BoundaryLoading =
        {
            Identity = NodeId 40
            Binding = NodeId 41
            Selector = "fixture.loading"
            Contract = contract
            Platform = NodeId 42
            Core = NodeId 43
            DeclarationFacts = Map.empty
            Participants = Set.empty
        }

    let declaration: BoundaryImport =
        {
            Identity = NodeId 44
            Binding = NodeId 30
            Scope = NodeId 35
            Library = "c"
            Symbol = "fixture_extern"
            CallingConvention = "cdecl"
            DeclarationPath = [ NodeId 30 ]
            Parameters = []
            Result = None
            Participants = Set.empty
            SourceTypes = Map.empty
            DeclarationFacts = Map.empty
        }

    let entry: BoundaryEntry =
        {
            Formation = NodeId 31
            Operand = NodeId 30
            Import = declaration.Identity
            Declaration = NodeId 30
            Loading = loading.Identity
            SourceType = ty
            Transport = Set.ofList [ NodeId 31; NodeId 32; NodeId 33 ]
            Participants = Set.empty
        }

    let call: BoundaryCall =
        {
            Site = NodeId 34
            Import = declaration.Identity
            Resource = None
            Callee = NodeId 33
            Entry = Some entry.Formation
            Arguments = []
            ErasedUnitArguments = []
            Result = None
            ResultAdaptation = None
            Participants = Set.empty
            SourceTypes = Map.empty
        }

    let graph = revision nodes

    { graph with
        Codata =
            { graph.Codata with
                FunctionPointers = Map.ofList [ entry.Formation, FunctionPointerPlan.ExternAddress entry.Formation ]
            }
        Emission =
            { graph.Emission with
                Callable =
                    { graph.Emission.Callable with
                        ValueShapes = nodes |> List.map (fun n -> n.Id, CallableValueShape.Data n.Id) |> Map.ofList
                        AliasTargets =
                            nodes
                            |> List.map (fun n ->
                                n.Id,
                                if n.Id = NodeId 32 || n.Id = NodeId 33 then
                                    NodeId 31
                                else
                                    n.Id)
                            |> Map.ofList
                        ClosedData = nodes |> List.map _.Id |> Set.ofList
                    }
                Boundary =
                    { graph.Emission.Boundary with
                        Loading = Some loading
                        Entries = Map.ofList [ entry.Formation, entry ]
                        Imports = Map.ofList [ declaration.Identity, declaration ]
                        Calls = Map.ofList [ call.Site, call ]
                        DeclarationLeaves = Set.singleton (NodeId 30)
                    }
            }
    }
    |> declareBindingReadings

let private importedTraversal (graph: Revision) =
    let accumulator = MLIRAccumulator.empty ()
    let ctx = context graph (NodeId 35) accumulator

    let witness (ctx: WitnessContext) (node: SemanticNode) =
        if node.Id = NodeId 34 then
            match
                Alex.XParsec.PSGCombinators.tryMatchWithDiagnostics
                    Alex.Patterns.PlatformPatterns.pBoundaryCall
                    ctx.Graph
                    node
                    ctx.Zipper
                    ctx.Coeffects
                    ctx.Accumulator
            with
            | Ok((ops, result), _) ->
                {
                    InlineOps = ops
                    TopLevelOps = []
                    Result = result
                }
            | Result.Error reason -> WitnessOutput.error reason
        elif node.Id = NodeId 30 || node.Id = NodeId 35 then
            {
                InlineOps = []
                TopLevelOps = []
                Result = TRVoid
            }
        else
            combineWitnesses
                [
                    Alex.Witnesses.FunctionPointerWitness.nanopass
                    Alex.Witnesses.BindingWitness.nanopass
                    Alex.Witnesses.VarRefWitness.nanopass
                ]
                ctx
                node

    visitAllNodes witness ctx graph.Nodes[NodeId 35] ctx.TraversalVisited
    ctx

/// Component values declare storage and reservation explicitly. This is not
/// compiler source admission; the real module publication is checked separately.
let private nativeModuleSlotFixture () =
    let graph = importedFixture ()

    let space: BAREWire.Platform.MemorySpace =
        {
            Name = "program"
            Kind = "ram"
            Capacity = 4096L
            Alignment = 8
            Granularity = 8
            Growth = "fixed"
            Access = "rw"
            Base = None
            Notes = ""
            MapKind = ""
            Since = ""
            Until = ""
        }

    let storage: ProgramStorageEntry =
        {
            Identity = ProgramStorageIdentity.BindingSlot(NodeId 32)
            SourceType = graph.Emission.Boundary.Entries[NodeId 31].SourceType
            Shape = ProgramStorageShape.NativeEntry(NodeId 31)
            Bytes = 8
            Alignment = 8
            SpaceNode = NodeId 50
            Space = space
            Participants = Set.ofList [ NodeId 31; NodeId 32; NodeId 50 ]
        }

    let projection = graph.Emission.Storage

    let inventory =
        { projection.ProgramStorage with
            Entries = Map.ofList [ storage.Identity, storage ]
        }

    storage,
    { graph with
        Emission =
            { graph.Emission with
                Storage =
                    { projection with
                        ProgramStorage = inventory
                        SlotAuthorities = Set.singleton (NodeId 32)
                    }
            }
    }

let private nativeSlotPattern graph site pattern accumulator =
    matchAt pattern (focus graph graph.Nodes[site]) 64 accumulator

let private requireSlotPattern =
    function
    | Ok(result, _) -> result
    | Result.Error error -> failwith error

let private nativeSlotTypeFixture () =
    let _, graph = nativeModuleSlotFixture ()
    let numeric = graph.Emission.Numeric

    let numeric =
        { numeric with
            OccurrenceRepresentations =
                numeric.OccurrenceRepresentations.Add(
                    NodeId 32,
                    Result.Error "Native callable values require their source-settled entry and callable components (CCS8410)."
                )
        }

    { graph with
        Emission =
            { graph.Emission with
                Numeric = numeric
            }
    }

[<Fact>]
let ``native module type read consumes its exact entry slot`` () =
    let graph = nativeSlotTypeFixture ()
    Assert.Equal(TFunc([], []), Alex.CodeGeneration.TypeMapping.valueTypeAt graph (NodeId 32))

[<Fact>]
let ``native module type read refuses withdrawn binding transport`` () =
    let graph = nativeSlotTypeFixture ()
    let boundary = graph.Emission.Boundary
    let entry = boundary.Entries[NodeId 31]

    let entry =
        { entry with
            Transport = entry.Transport.Remove(NodeId 32)
        }

    let boundary =
        { boundary with
            Entries = boundary.Entries.Add(entry.Formation, entry)
        }

    let graph =
        { graph with
            Emission =
                { graph.Emission with
                    Boundary = boundary
                }
        }

    let error =
        Assert.Throws<System.Exception>(fun () -> Alex.CodeGeneration.TypeMapping.valueTypeAt graph (NodeId 32) |> ignore)

    Assert.Contains("Native entry slot differs from its original immutable formation binding.", error.Message)

[<Fact>]
let ``native module type read retains ordinary numeric refusal`` () =
    let graph = nativeSlotTypeFixture ()
    let storage = graph.Emission.Storage

    let storage =
        { storage with
            ProgramStorage =
                { storage.ProgramStorage with
                    Entries = Map.empty
                }
        }

    let graph =
        { graph with
            Emission =
                { graph.Emission with
                    Storage = storage
                }
        }

    let error =
        Assert.Throws<System.Exception>(fun () -> Alex.CodeGeneration.TypeMapping.valueTypeAt graph (NodeId 32) |> ignore)

    Assert.Contains("value occurrence 32 has no source-published representation", error.Message)
    Assert.Contains("CCS8410", error.Message)

[<Fact>]
let ``native entry module slot keeps typed initialization and reload`` () =
    let storage, graph = nativeModuleSlotFixture ()
    let accumulator = MLIRAccumulator.empty ()
    let functionType = TFunc([], [])

    let initialized =
        nativeSlotPattern
            graph
            (NodeId 32)
            (Alex.Patterns.MemRefPatterns.pGlobalSlotInit (NodeId 32) "module_entry" (V(31, 0)) functionType)
            accumulator
        |> requireSlotPattern

    match initialized with
    | [ MemRefOp(MemRefOp.GetGlobal(_, "module_entry", container)); NativeEntrySlotStore(identity, formation, slot, value) ], TRValue held ->
        Assert.Equal(storage.Identity, identity)
        Assert.Equal(NodeId 31, formation)
        Assert.Equal(TMemRefStatic(8, TInt(IntWidth 8)), container)
        Assert.Equal(slot, held)
        Assert.Equal(functionType, value.Type)
    | other -> failwithf "Typed native slot initialization differed: %A" other

    let reloaded =
        nativeSlotPattern
            graph
            (NodeId 33)
            (Alex.Patterns.MemRefPatterns.pGlobalSlotLoad (NodeId 32) (NodeId 33) "module_entry" TIndex)
            accumulator
        |> requireSlotPattern

    match reloaded with
    | [ MemRefOp(MemRefOp.GetGlobal(_, "module_entry", container)); NativeEntrySlotLoad(identity, formation, slot, result) ], TRValue held ->
        Assert.Equal(storage.Identity, identity)
        Assert.Equal(NodeId 31, formation)
        Assert.Equal(container, slot.Type)
        Assert.Equal(functionType, result.Type)
        Assert.Equal(result, held)
    | other -> failwithf "Typed native slot reload differed: %A" other

    let declarations = MLIRAccumulator.drainPendingStaticGlobals accumulator
    Assert.Equal(2, declarations.Length)
    Assert.Contains(NativeEntrySlotDecl("module_entry", storage, NodeId 31, functionType), declarations)
    Assert.Contains(GlobalMemref("module_entry", TMemRefStatic(8, TInt(IntWidth 8)), Some storage), declarations)

[<Theory>]
[<InlineData("entry", "Native entry slot has no matching current source formation.")>]
[<InlineData("import", "Native entry slot has no matching current import and selected loading account.")>]
[<InlineData("loading", "Native entry slot has no matching current import and selected loading account.")>]
let ``native entry module slot refuses withdrawn account`` (withdrawal: string) (reason: string) =
    let storage, graph = nativeModuleSlotFixture ()
    let boundary = graph.Emission.Boundary

    let changed =
        match withdrawal with
        | "entry" -> { boundary with Entries = Map.empty }
        | "import" -> { boundary with Imports = Map.empty }
        | "loading" -> { boundary with Loading = None }
        | _ -> failwith "Unknown fixture withdrawal"

    let graph =
        { graph with
            Emission =
                { graph.Emission with
                    Boundary = changed
                }
        }

    match nativeSlotPattern graph (NodeId 32) (Alex.Patterns.MemoryPatterns.pNativeEntrySlot storage) (MLIRAccumulator.empty ()) with
    | Result.Error error -> Assert.Contains(reason, error)
    | other -> failwithf "Withdrawn native slot account was admitted: %A" other

[<Fact>]
let ``native entry module slot refuses changed initializer type`` () =
    let _, graph = nativeModuleSlotFixture ()

    let pattern =
        Alex.Patterns.MemRefPatterns.pGlobalSlotInit (NodeId 32) "module_entry" (V(31, 0)) (TInt(IntWidth 64))

    match nativeSlotPattern graph (NodeId 32) pattern (MLIRAccumulator.empty ()) with
    | Result.Error error -> Assert.Contains("Native entry slot differs from its original imported function signature.", error)
    | other -> failwithf "Changed native initializer type was admitted: %A" other

[<Fact>]
let ``native entry module slot refuses mutable store`` () =
    let _, graph = nativeModuleSlotFixture ()

    let pattern =
        Alex.Patterns.MemRefPatterns.pGlobalSlotStore (NodeId 32) (NodeId 32) "module_entry" (V(31, 0)) (TFunc([], []))

    match nativeSlotPattern graph (NodeId 32) pattern (MLIRAccumulator.empty ()) with
    | Result.Error error -> Assert.Contains("Native entry module slots do not admit mutable stores.", error)
    | other -> failwithf "Mutable native slot store was admitted: %A" other

[<Fact>]
let ``native entry module slot serializes stock typed placeholders`` () =
    let storage, _ = nativeModuleSlotFixture ()
    let functionType = TFunc([], [])

    let slot =
        {
            SSA = V(32, 0)
            Type = TMemRefStatic(8, TInt(IntWidth 8))
        }

    let value = { SSA = V(31, 0); Type = functionType }
    let result = { SSA = V(33, 2); Type = functionType }

    let ops =
        [
            NativeEntrySlotDecl("module_entry", storage, NodeId 31, functionType)
            NativeEntrySlotStore(storage.Identity, NodeId 31, slot, value)
            NativeEntrySlotLoad(storage.Identity, NodeId 31, slot, result)
        ]

    let text =
        ops
        |> List.map (Alex.Dialects.Core.Serialize.opToString (Ok 64))
        |> String.concat "\n"

    Assert.Contains("func.func private @__clef_native_entry_slot_store_32(memref<8xi8>, () -> ())", text)
    Assert.Contains("func.func private @__clef_native_entry_slot_load_32(memref<8xi8>) -> (() -> ())", text)
    Assert.Contains("func.call @__clef_native_entry_slot_store_32", text)
    Assert.Contains("%v33_2 = func.call @__clef_native_entry_slot_load_32", text)
    Assert.DoesNotContain("memref<1x(", text)
    Assert.DoesNotContain("!llvm.ptr", text)

[<Fact>]
let ``imported pointer initialization and immutable read precede the indirect call`` () =
    let graph = importedFixture ()
    Assert.Equal(Some(NodeId 31), graph.Emission.Boundary.Calls[NodeId 34].Entry)
    let ctx = graph |> importedTraversal
    Assert.Empty ctx.Accumulator.Errors
    let formed = MLIRAccumulator.recallNode (NodeId 31) ctx.Accumulator
    Assert.Equal(formed, MLIRAccumulator.recallNode (NodeId 32) ctx.Accumulator)
    Assert.Equal(formed, MLIRAccumulator.recallNode (NodeId 33) ctx.Accumulator)
    let ops = ScopeContext.getOps ctx.ScopeContext.Value

    match ops with
    | [ FuncOp(FuncConstant(_, "fixture_extern", _)); FuncOp(FuncCallIndirect(_, pointer, [])) ] ->
        Assert.Equal((Option.get formed |> fst), pointer)
    | other -> failwithf "Expected one formation and its actual indirect call: %A" other

/// Current-data consumer controls only: target conversion is intentionally
/// pending, so neither selected case may borrow plain native-entry lowering.
[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``optional native entry boundary refuses Some and None before operand lowering`` present =
  let graph = importedFixture ()
  let boundary = graph.Emission.Boundary
  let call = boundary.Calls[NodeId 34]
  let account: BoundaryOptionalEntry =
    { Construction = NodeId 33; CaseOrdinal = if present then 1 else 0
      Payload = if present then Some(NodeId 31) else None
      Formation = if present then Some(NodeId 31) else None
      Transport = Set.singleton (NodeId 33)
      Obligation = NodeId 70 }
  let operand: BoundaryOperand =
    { Actual = NodeId 33; Formal = NodeId 71; Abi = BoundaryScalar.Entry(NodeId 72)
      Adaptation = None; OptionalEntry = Some (BoundaryOptionalEntryChoice.Direct account) }
  let changed =
    { boundary with
        Calls =
          boundary.Calls.Add(call.Site,
            {call with Arguments = [operand]; Participants = Set.ofList [NodeId 31; NodeId 33; call.Site]}) }
  let graph = { graph with Emission = {graph.Emission with Boundary = changed} }
  let accumulator = MLIRAccumulator.empty ()
  let ctx = context graph call.Site accumulator
  match Alex.XParsec.PSGCombinators.tryMatchWithDiagnostics
          Alex.Patterns.PlatformPatterns.pBoundaryCall graph graph.Nodes[call.Site]
          ctx.Zipper ctx.Coeffects accumulator with
  | Result.Error reason ->
    Assert.Equal((if present then "Optional native-entry boundary conversion requires target-pathway authority; this consumer does not admit it."
                  else "Optional native-entry absence conversion lacks its exact current source account."), reason)
  | Result.Ok result -> failwithf "Optional native entry was lowered as a plain entry: %A" result
  Assert.Empty accumulator.AllOps
  Assert.Null(MLIRAccumulator.recallNode operand.Actual accumulator)
  Assert.Null(MLIRAccumulator.recallNode call.Site accumulator)

let private conditionalOptionalBoundaryFixture reversed =
  let ordinarySig = functionFrom intType intType
  let fnPtrType =
    TypeIdentity.Application(
      { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [TypeParamKind.Type]; NativeKind = Some NTUKind.NTUfnptr },
      [ordinarySig])
  let optionType = optionOf fnPtrType
  let consumerSig = functionFrom optionType unitType
  let callerSig = functionFrom boolType unitType
  let cbFormal = node 10 (SemanticKind.PatternBinding "x") intType [] (Some 12)
  let cbBody = node 11 (SemanticKind.VarRef("x", Some(NodeId 10))) intType [] (Some 12)
  let cbLambda = node 12 (SemanticKind.Lambda(["x", intType, NodeId 10], NodeId 11, [], None, LambdaContext.RegularClosure)) ordinarySig [10; 11] (Some 20)
  let cbBinding = node 20 (SemanticKind.Binding("callback", false, false, None)) ordinarySig [12] (Some 50)
  let ofFunctionNode =
    node 21
      (SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "ofFunction"; Category = IntrinsicCategory.Pure; FullName = "FnPtr.ofFunction" })
      (functionFrom ordinarySig fnPtrType) [] (Some 23)
  let cbRef = node 22 (SemanticKind.VarRef("callback", Some(NodeId 20))) ordinarySig [] (Some 23)
  let formation = node 23 (SemanticKind.Application(NodeId 21, [NodeId 22])) fnPtrType [21; 22] (Some 25)
  let condRef = node 24 (SemanticKind.VarRef("pred", Some(NodeId 31))) boolType [] (Some 27)
  let someNode = node 25 (SemanticKind.DUConstruct("Some", 1, Some(NodeId 23), None)) optionType [23] (Some 27)
  let noneNode = node 26 (SemanticKind.DUConstruct("None", 0, None, None)) optionType [] (Some 27)
  let whenTrueNode, whenFalseNode = if reversed then noneNode, someNode else someNode, noneNode
  let selectNode =
    node 27 (SemanticKind.IfThenElse(condRef.Id, whenTrueNode.Id, Some whenFalseNode.Id)) optionType
      [NodeId.value condRef.Id; NodeId.value whenTrueNode.Id; NodeId.value whenFalseNode.Id] (Some 30)
  let tagNode =
    { node 28 (SemanticKind.DUGetTag(selectNode.Id, optionType)) intType [27] (Some 30) with
        ValueRange = Some(ValueRange.Bounded(0I, 1I)) }
  let calleeLeaf = node 29 (SemanticKind.PatternBinding "consume_callback") consumerSig [] (Some 30)
  let callNode = node 30 (SemanticKind.Application(calleeLeaf.Id, [selectNode.Id])) unitType [29; 27; 28] (Some 32)
  let predFormal = node 31 (SemanticKind.PatternBinding "pred") boolType [] (Some 32)
  let callerLambda = node 32 (SemanticKind.Lambda(["pred", boolType, NodeId 31], NodeId 30, [], None, LambdaContext.RegularClosure)) callerSig [31; 30] (Some 33)
  let callerBinding = node 33 (SemanticKind.Binding("dispatch", false, false, None)) callerSig [32] (Some 34)
  let rootSeq = node 34 (SemanticKind.Sequential [NodeId 20; NodeId 33]) unitType [20; 33] None
  let moduleScope = { node 50 (SemanticKind.ModuleDef("Native", [NodeId 20])) unitType [] None with IsReachable = false }
  let liveNodes =
    [ cbFormal; cbBody; cbLambda; cbBinding; ofFunctionNode; cbRef; formation
      condRef; someNode; noneNode; selectNode; tagNode; calleeLeaf; callNode
      predFormal; callerLambda; callerBinding; rootSeq; moduleScope ]
  let participant role ordinal group identity : Participant =
    { Role = role; Ordinal = ordinal; Group = group; Node = identity }
  let rowParticipants (row: CallableAggregateValue) =
    [ yield participant ParticipantRole.AggregateValue 0 row.Occurrence row.Occurrence
      yield participant ParticipantRole.AggregateSource 0 row.Occurrence row.Aggregate
      yield participant ParticipantRole.AggregateSlot 0 row.Occurrence row.Slot
      for ordinal, input in List.indexed row.FormationInputs do
        yield participant ParticipantRole.AggregateInput ordinal row.Occurrence input
      for actual in Option.toList row.Value do
        yield participant ParticipantRole.AggregateWrite 0 row.Occurrence actual
      for alt in row.Alternatives do
        yield participant ParticipantRole.CallableCarrier alt.Ordinal row.Occurrence alt.Carrier
        yield participant ParticipantRole.CallableFormation alt.Ordinal row.Occurrence alt.Formation
        yield participant ParticipantRole.CallableContract alt.Ordinal row.Occurrence alt.Contract ]
  let intSlot = SettledSlot.Integer(64, Some "int")
  let intScalar = ValueRepresentation.Scalar intSlot
  let lifetime : ProgramImageCodeLifetime = { Module = moduleScope.Id; Binding = cbBinding.Id; Implementation = cbLambda.Id }
  let lifetimeParticipants =
    [moduleScope.Id; cbBinding.Id; cbLambda.Id]
    |> List.mapi (fun ordinal id -> participant ParticipantRole.CallableLifetime ordinal cbLambda.Id id)
  let sourcePremiseParticipants =
    [moduleScope.Id; cbBinding.Id; cbLambda.Id]
    |> List.mapi (fun ordinal id -> participant ParticipantRole.Source ordinal cbLambda.Id id)
  let premise form text numbers references children parent sourceType embedded reachable : BoundarySourcePremise =
    { Shape = { Form = form; Text = text; Numbers = numbers; References = references
                Children = children; Parent = parent; SourceType = sourceType }
      EmbeddedTypes = embedded; ConstructorFacts = []; Reachable = reachable; Range = None
      ExternLibrary = None; ExternSymbol = None; HasExtern = false; Metadata = Map.empty }
  let premises =
    Map.ofList [
      moduleScope.Id, premise "module" ["Native"] [] [cbBinding.Id] [] None unitType [] false
      cbBinding.Id, premise "binding" ["callback"; "no-declaration-root"] [0I; 0I] [cbLambda.Id] [cbLambda.Id] (Some moduleScope.Id) ordinarySig [] true
      cbLambda.Id, premise "lambda" ["RegularClosure"; "x"] [1I; 0I; 0I] [cbFormal.Id; cbBody.Id] [cbFormal.Id; cbBody.Id] (Some cbBinding.Id) ordinarySig [intType] true ]
  let target : BoundaryPlatformPremise =
    { Id = "alex-conditional-optional-entry"; Description = None; LibraryPath = None; Loading = None; SourcePaths = Set.singleton range.File
      Architecture = Some "x86_64"; OS = Some "linux"; RuntimeClaim = Some RuntimeModel.Libc; Substrate = Some SubstrateKind.CPU
      Dimensions = Map.ofList ["Pointer", 64; "Register", 64]; Representations = Map.empty; EndpointReturns = Map.empty }
  let contract : CallableContract =
    { Identity = cbLambda.Id; Kind = CallableKind.NativeEntry
      Convention = CallableConvention.CompilerOwnedPortable {
        Target = target
        ParameterConversions = [0, CallableConversion.Identity intScalar]
        ResultConversion = CallableConversion.Identity intScalar
        CodeLifetime = lifetime }
      ParameterTypes = [intType]; OmittedParameters = []
      ParameterRepresentations = [0, intScalar]
      ResultType = intType; ResultRepresentation = intScalar
      EnvironmentBytes = None; SourcePremises = premises
      Participants =
        [ participant ParticipantRole.CallableContract 0 cbLambda.Id cbLambda.Id
          participant ParticipantRole.CallableImplementation 0 cbLambda.Id cbLambda.Id
          participant ParticipantRole.CalleeParameter 0 cbLambda.Id cbFormal.Id
          participant ParticipantRole.CalleeBody 0 cbLambda.Id cbBody.Id ]
        @ lifetimeParticipants @ sourcePremiseParticipants }
  let nativeCarrier : CallableCarrier =
    { Occurrence = formation.Id; Kind = CallableKind.NativeEntry; Formation = formation.Id
      EnvironmentValue = None; Contract = Result.Ok contract.Identity; Lifetime = lifetimeParticipants
      SourceType = fnPtrType; Implementation = cbLambda.Id
      Parameters = ["x", intType, cbFormal.Id]; ParameterShapes = [CallableValueShape.Data cbFormal.Id]
      OmittedParameters = Set.empty; Result = cbBody.Id; ResultShape = CallableValueShape.Data cbBody.Id
      Environment = None }
  let cbDeclaration : CallableEmissionDeclaration =
    { Lookup = cbLambda.Id; Implementation = cbLambda.Id
      Parameters = ["x", intType, cbFormal.Id]; Result = cbBody.Id; Context = LambdaContext.RegularClosure
      Captures = []; Name = CallableSymbolName.ModuleBinding("Native", "callback"); Parent = Some cbBinding.Id
      Participants = Set.ofList [cbFormal.Id; cbBody.Id; cbLambda.Id] }
  let slotId = NodeId 99
  let slot : CallableAggregateSlot =
    { Identity = slotId; AggregateType = optionType; Declaration = None; DeclarationFacts = []
      Path = [CallableAggregatePathStep.UnionPayload(1, 0)]; SourceType = fnPtrType
      Contract = Result.Ok contract.Identity
      Participants = [ participant ParticipantRole.AggregateSlot 0 slotId slotId
                       participant ParticipantRole.CallableContract 0 slotId contract.Identity ] }
  let alternative : CallableAggregateAlternative =
    { Ordinal = 0; Carrier = formation.Id; Formation = formation.Id; EnvironmentValue = None
      Contract = contract.Identity; Adapter = None; EnvironmentPlacement = None }
  let selector : CallableAggregateSelector =
    { Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None }
  let someRow : CallableAggregateValue =
    { Occurrence = someNode.Id; Aggregate = someNode.Id; Slot = slotId
      Alternatives = [alternative]; Selector = Some selector
      FormationInputs = [formation.Id]; Value = Some formation.Id; SelectedAlternative = Some 0
      Operation = CallableAggregateOperation.Construct; Frontier = None
      Tag = Some { Constructor = someNode.Id; TagRead = None; CaseOrdinal = 1; PayloadOrdinal = Some 0; Payload = Some formation.Id
                   Participants = [ participant ParticipantRole.AggregateConstructor 0 someNode.Id someNode.Id
                                    participant ParticipantRole.AggregatePayload 0 someNode.Id formation.Id ] }
      Selection = None; Bytes = 0; Alignment = 1; Participants = []; ResultRetirement = None }
    |> fun row -> { row with Participants = rowParticipants row }
  let noneRow : CallableAggregateValue =
    { Occurrence = noneNode.Id; Aggregate = noneNode.Id; Slot = slotId
      Alternatives = []; Selector = None
      FormationInputs = []; Value = None; SelectedAlternative = None
      Operation = CallableAggregateOperation.Construct; Frontier = None
      Tag = Some { Constructor = noneNode.Id; TagRead = None; CaseOrdinal = 0; PayloadOrdinal = None; Payload = None
                   Participants = [ participant ParticipantRole.AggregateConstructor 0 noneNode.Id noneNode.Id ] }
      Selection = None; Bytes = 0; Alignment = 1; Participants = []; ResultRetirement = None }
    |> fun row -> { row with Participants = rowParticipants row }
  let selectRow : CallableAggregateValue =
    { Occurrence = selectNode.Id; Aggregate = selectNode.Id; Slot = slotId
      Alternatives = [alternative]; Selector = Some selector
      FormationInputs = [condRef.Id; whenTrueNode.Id; whenFalseNode.Id]; Value = None; SelectedAlternative = None
      Operation = CallableAggregateOperation.Select; Frontier = None; Tag = None
      Selection = Some { Condition = condRef.Id; WhenTrue = whenTrueNode.Id; WhenFalse = whenFalseNode.Id }
      Bytes = 0; Alignment = 1; Participants = []; ResultRetirement = None }
    |> fun row ->
      { row with
          Participants =
            rowParticipants row
            @ [ participant ParticipantRole.Source 0 selectNode.Id predFormal.Id
                participant ParticipantRole.Source 1 selectNode.Id callerLambda.Id ] }
  let aggregateValues =
    Map.ofList [
      someNode.Id, [someRow]
      noneNode.Id, [noneRow]
      selectNode.Id, [selectRow] ]
  let invocationId, invocationScope, invocationRecord = NodeId 700, NodeId 701, NodeId 702
  let importId, importBinding, formalParam = NodeId 703, NodeId 704, NodeId 705
  let scopedDescriptorType =
    TypeIdentity.Application(
      { Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "Descriptors.ScopedCallbackDescriptor" }
        Parameters = []; NativeKind = None }, [])
  let importFacts =
    Map.ofList [
      importBinding, { Form = "binding"; Text = ["consume_callback"]; Numbers = [0I; 0I]; References = []; Children = []; Parent = Some moduleScope.Id; SourceType = consumerSig }
      formalParam, { Form = "pattern-binding"; Text = ["cb"]; Numbers = []; References = []; Children = []; Parent = Some importBinding; SourceType = optionType }
      invocationId, { Form = "quotation"; Text = []; Numbers = []; References = []; Children = []; Parent = None; SourceType = unitType }
      invocationScope, { Form = "quotation"; Text = []; Numbers = []; References = [invocationRecord]; Children = [invocationRecord]; Parent = None; SourceType = scopedDescriptorType }
      invocationRecord, { Form = "record"; Text = []; Numbers = []; References = []; Children = []; Parent = Some invocationScope; SourceType = scopedDescriptorType } ]
  let imported : BoundaryImport =
    { Identity = importId; Binding = importBinding; Scope = moduleScope.Id
      Library = "c"; Symbol = "consume_callback"; CallingConvention = "CDecl"
      DeclarationPath = [importBinding]
      Parameters = [formalParam, BoundaryScalar.Entry invocationId]
      Result = None
      Participants = Set.ofList [importId; importBinding; formalParam; invocationId; invocationScope; invocationRecord; moduleScope.Id]
      SourceTypes = Map.ofList [formalParam, optionType]
      DeclarationFacts = importFacts }
  let invocation : BoundaryCallbackInvocation =
    { Identity = invocationId; Import = importId; Parameter = 0; Formal = formalParam; Scope = invocationScope
      Contract =
        { Binding = "Native.consume_callback"; Parameter = 0; Scope = "during_call"
          Signature =
            { Parameters = [| { Name = "x"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 64); PassBy = BAREWire.Descriptors.PassBy.Value } |]
              ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 64)
              CallingConvention = BAREWire.Descriptors.CallConv.CDecl }
          Hypothesis = { Identity = "callback-during-call"; Version = "1"; Source = "fixture" } }
      Signature = { Parameters = [BoundaryScalar.Integer(64, true)]; Result = Some(BoundaryScalar.Integer(64, true)); CallingConvention = "CDecl" }
      Extent = BoundaryCallbackExtent.DuringCall
      Participants = Set.ofList [invocationId; invocationScope; importId; formalParam] }
  let closedEntry : BoundaryClosedEntry =
    { Formation = formation.Id; Operand = cbRef.Id; Declaration = cbBinding.Id; Implementation = cbLambda.Id
      Formals = [cbFormal.Id]; Body = cbBody.Id; Lifetime = lifetime; Invocation = invocationId
      ParameterAdaptations = [None]; ResultAdaptation = None; Registrations = Map.empty
      Transport = Set.ofList [cbRef.Id; formation.Id; someNode.Id; selectNode.Id]
      Participants =
        Set.ofList [
          cbFormal.Id; cbBody.Id; cbLambda.Id; cbBinding.Id; ofFunctionNode.Id; cbRef.Id
          formation.Id; someNode.Id; selectNode.Id; callNode.Id; moduleScope.Id; invocationId ] }
  let absenceQuote, absenceBinding, absenceRecord = NodeId 710, NodeId 711, NodeId 712
  let absFieldBinding, absFieldParam, absFieldHyp = NodeId 713, NodeId 714, NodeId 715
  let absHypId, absHypVer, absHypSrc = NodeId 716, NodeId 717, NodeId 718
  let absenceRecordType =
    TypeIdentity.Application(
      { Declaration = { Module = ["BAREWire"; "Descriptors"]; Name = "Descriptors.CallbackAbsenceContract" }
        Parameters = []; NativeKind = None }, [])
  let absenceContract : BAREWire.Descriptors.CallbackAbsenceContract =
    { Binding = "Native.consume_callback"; Parameter = 0
      Hypothesis = { Identity = "callback-absence-ok"; Version = "1"; Source = "fixture" } }
  let absenceFacts =
    Map.ofList [
      absenceBinding, { Form = "binding"; Text = ["consumeAbsence"]; Numbers = [0I; 0I]; References = [absenceQuote]; Children = [absenceQuote]; Parent = Some moduleScope.Id; SourceType = absenceRecordType }
      absenceQuote, { Form = "quotation"; Text = []; Numbers = []; References = [absenceRecord]; Children = [absenceRecord]; Parent = Some absenceBinding; SourceType = absenceRecordType }
      absenceRecord, { Form = "record"; Text = ["Binding"; "Parameter"; "Hypothesis"]; Numbers = []; References = [absFieldBinding; absFieldParam; absFieldHyp]; Children = [absFieldBinding; absFieldParam; absFieldHyp]; Parent = Some absenceQuote; SourceType = absenceRecordType }
      absFieldBinding, { Form = "string"; Text = ["Native.consume_callback"]; Numbers = []; References = []; Children = []; Parent = Some absenceRecord; SourceType = stringType }
      absFieldParam, { Form = "integer"; Text = []; Numbers = [0I]; References = []; Children = []; Parent = Some absenceRecord; SourceType = intType }
      absFieldHyp, { Form = "record"; Text = ["Identity"; "Version"; "Source"]; Numbers = []; References = [absHypId; absHypVer; absHypSrc]; Children = [absHypId; absHypVer; absHypSrc]; Parent = Some absenceRecord; SourceType = unitType }
      absHypId, { Form = "string"; Text = ["callback-absence-ok"]; Numbers = []; References = []; Children = []; Parent = Some absFieldHyp; SourceType = stringType }
      absHypVer, { Form = "string"; Text = ["1"]; Numbers = []; References = []; Children = []; Parent = Some absFieldHyp; SourceType = stringType }
      absHypSrc, { Form = "string"; Text = ["fixture"]; Numbers = []; References = []; Children = []; Parent = Some absFieldHyp; SourceType = stringType } ]
  let absence : BoundaryCallbackAbsence =
    { Quote = absenceQuote; DescriptorBinding = absenceBinding; Record = absenceRecord
      Import = importId; Parameter = 0; Formal = formalParam; Invocation = invocationId
      Contract = absenceContract
      SourcePath = [absenceQuote; absenceRecord]
      Inputs =
        [ CallbackAbsenceInputRole.Binding, [absFieldBinding]
          CallbackAbsenceInputRole.Parameter, [absFieldParam]
          CallbackAbsenceInputRole.Hypothesis, [absFieldHyp]
          CallbackAbsenceInputRole.HypothesisIdentity, [absHypId]
          CallbackAbsenceInputRole.HypothesisVersion, [absHypVer]
          CallbackAbsenceInputRole.HypothesisSource, [absHypSrc] ]
      DeclarationFacts = absenceFacts }
  let presentClaimId, absentClaimId = NodeId 720, NodeId 721
  let presentArm : BoundaryOptionalEntry =
    { Construction = someNode.Id; CaseOrdinal = 1; Payload = Some formation.Id; Formation = Some formation.Id
      Transport = Set.ofList [someNode.Id; selectNode.Id]; Obligation = presentClaimId }
  let absentArm : BoundaryOptionalEntry =
    { Construction = noneNode.Id; CaseOrdinal = 0; Payload = None; Formation = None
      Transport = Set.ofList [noneNode.Id; selectNode.Id]; Obligation = absentClaimId }
  let whenTrueArm, whenFalseArm = if reversed then absentArm, presentArm else presentArm, absentArm
  let presentClaim : ObligationInfo =
    { Id = "opt_present_720"; Kind = "foreign-optional-entry-conversion-0"; Logic = "QF_LIA"
      Statement = "The exact source Some selection has complete finite native-choice plan correspondence; target realization remains an artifact obligation."
      Source = "alex-test.clef:1"; Refs = []
      Body =
        ObligationBody.OptionalEntryArgumentConversion {
          Call = callNode.Id; Parameter = 0; Actual = selectNode.Id; Construction = someNode.Id
          SourceCase = 1; Payload = formation.Id; Formation = formation.Id; Invocation = invocationId
          Arms =
            [ { CaseOrdinal = 0; Choice = OptionalEntryPlanChoice.PendingAbsence; Formation = None }
              { CaseOrdinal = 1; Choice = OptionalEntryPlanChoice.ClosedEntry; Formation = Some formation.Id } ]
          ResultRetirement = None } }
  let absentClaim : ObligationInfo =
    { Id = "opt_absent_721"; Kind = "foreign-optional-entry-conversion-0"; Logic = "QF_LIA"
      Statement = "The exact source None selection has complete finite absence-choice correspondence under its external binding hypothesis; target realization remains an artifact obligation."
      Source = "alex-test.clef:1"; Refs = []
      Body =
        ObligationBody.OptionalEntryAbsenceArgumentConversion {
          Call = callNode.Id; Parameter = 0; Actual = selectNode.Id; Construction = noneNode.Id
          SourceCase = 0; Absence = absenceQuote
          Arms =
            [ { CaseOrdinal = 0; Choice = OptionalEntryAbsencePlanChoice.AbsentEntry }
              { CaseOrdinal = 1; Choice = OptionalEntryAbsencePlanChoice.RequiresClosedEntry } ]
          ResultRetirement = None } }
  let buildDependencyAccounts (graph: Revision) =
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
      let carriers = values |> List.collect _.Alternatives |> List.map _.Carrier |> List.distinct |> List.map (fun id -> c.Carriers[id])
      let contracts = [contract]
      let participants =
        (slots |> List.collect _.Participants)
        @ (values |> List.collect (fun row -> row.Participants @ (row.Tag |> Option.map _.Participants |> Option.defaultValue [])))
        @ (carriers |> List.collect _.Lifetime)
        @ (contracts |> List.collect _.Participants)
      let ids = participants |> List.map _.Node |> List.distinct
      let premiseIds = contracts |> List.collect (fun row -> row.SourcePremises.Keys |> Seq.toList) |> Set.ofList
      let sources =
        ids |> List.choose (fun id ->
          (if premiseIds.Contains id then None else graph.Nodes.TryFind id)
          |> Option.map (fun n -> { Node = id; Kind = n.Kind; Type = n.Type; Children = n.Children; Anchors = n.ObligationAnchors }))
      { Occurrence = occurrence; Slots = slots; Values = values; Carriers = carriers; Contracts = contracts
        Flows = []; Joins = []; Participants = participants; Sources = sources
        Claims = ids |> List.choose (fun id -> graph.CurrentClaims.TryFind id |> Option.map (fun row -> id, row))
        Symbols = [cbLambda.Id, cbDeclaration.Name]; Inactivity = []; MemoryPolicy = None }
    c.AggregateValues |> Map.map (fun occurrence _ -> account occurrence)
  let optionComponent = ValueRepresentation.CallableComponent(slotId, ValueRepresentation.Record([], Some([], 0, 1)))
  let optionRep = ValueRepresentation.Union(["None", []; "Some", [optionComponent]], Some(1, 1, 1))
  let unitRep = ValueRepresentation.Scalar SettledSlot.Unit
  let boolRep = ValueRepresentation.Scalar SettledSlot.Bool
  let tagRepresentation : NumericRepresentation =
    { Name = "int"; Capability = "native"; Family = "int"; Bits = 64
      MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "checked" }
  let tagCarrier : ScalarCarrier =
    { Site = tagNode.Id; SourceType = intType; Representation = Some tagRepresentation
      Declaration = None; Slot = intSlot; Range = ValueRange.Bounded(0I, 1I)
      Participants = Set.ofList [tagNode.Id; selectNode.Id]; Obligations = [] }
  let baseGraph = revision liveNodes |> declareBindingReadings
  let shapes =
    baseGraph.Nodes
    |> Map.remove moduleScope.Id
    |> Map.map (fun id _ ->
      if id = formation.Id then CallableValueShape.Callable id else CallableValueShape.Data id)
    |> Map.add formalParam (CallableValueShape.Data formalParam)
  let nonExecutableMeta = [formalParam]
  let aliasTargets =
    (baseGraph.Nodes |> Map.remove moduleScope.Id |> Map.map (fun id _ -> id))
    |> Map.add formalParam formalParam
  let closedData =
    shapes |> Map.toSeq |> Seq.choose (fun (id, s) -> match s with CallableValueShape.Data d -> Some d | _ -> None) |> Set.ofSeq
  let allSupportSet =
    Set.union ((baseGraph.Nodes |> Map.remove moduleScope.Id).Keys |> Set.ofSeq) (Set.ofList nonExecutableMeta)
  let supports =
    allSupportSet |> Seq.map (fun id -> id, allSupportSet) |> Map.ofSeq
  let sourceTypes =
    (baseGraph.Nodes |> Map.remove moduleScope.Id |> Map.map (fun _ n -> n.Type))
    |> Map.add formalParam optionType
  let representations =
    baseGraph.Nodes
    |> Map.remove moduleScope.Id
    |> Map.map (fun id n ->
      if id = formation.Id then
        Result.Error "A callable remains a function value and has no numeric data representation."
      elif id = someNode.Id || id = noneNode.Id || id = selectNode.Id then
        Result.Ok optionRep
      elif n.Type = intType then
        Result.Ok intScalar
      elif n.Type = boolType then
        Result.Ok boolRep
      else
        Result.Ok unitRep)
    |> Map.add formalParam (Result.Ok optionRep)
  let preAccountGraph =
    { baseGraph with
        Nodes = baseGraph.Nodes.Remove moduleScope.Id
        Platform = { Register = Ok 64; Pointer = Ok 64 }
        CurrentClaims = Map.ofList [presentClaimId, presentClaim; absentClaimId, absentClaim]
        Obligations = [presentClaim; absentClaim]
        Codata =
          { baseGraph.Codata with
              FunctionPointers = Map.ofList [formation.Id, FunctionPointerPlan.Address("Native.callback", cbLambda.Id)] }
        Emission =
          { baseGraph.Emission with
              Callable =
                { baseGraph.Emission.Callable with
                    Contracts = Map.ofList [contract.Identity, contract]
                    Carriers = Map.ofList [formation.Id, nativeCarrier]
                    Declarations = Map.ofList [cbLambda.Id, cbDeclaration]
                    Symbols = Map.ofList [cbLambda.Id, cbDeclaration.Name]
                    NativeEntries = Map.ofList [cbLambda.Id, "Native.callback"]
                    DefinitionOnlyBindings = Set.singleton cbBinding.Id
                    UnitNodes = Set.ofList [callNode.Id; rootSeq.Id]
                    AggregateSlots = Map.ofList [slotId, slot]
                    AggregateValues = aggregateValues
                    ValueShapes = shapes
                    AliasTargets = aliasTargets
                    Supports = supports
                    ClosedData = closedData }
              Numeric =
                { baseGraph.Emission.Numeric with
                    SourceTypes = sourceTypes
                    OccurrenceRepresentations = representations
                    Values = Map.ofList [tagNode.Id, tagCarrier] } } }
  let dependencies = buildDependencyAccounts preAccountGraph
  let ownSources = dependencies[selectNode.Id].Sources |> List.map _.Node |> Set.ofList
  let presentSupport =
    Set.unionMany [
      ownSources
      presentArm.Transport
      Set.ofList [callNode.Id; importId; calleeLeaf.Id; selectNode.Id; formalParam; someNode.Id]
      imported.Participants
      invocation.Participants ]
  let absentExtra = absence.DeclarationFacts |> Map.keys |> Set.ofSeq
  let absentSupport =
    Set.unionMany [
      ownSources
      absentArm.Transport
      Set.ofList [callNode.Id; importId; calleeLeaf.Id; selectNode.Id; formalParam; noneNode.Id]
      imported.Participants
      invocation.Participants
      absentExtra ]
  let callParticipants =
    Set.unionMany [
      presentSupport
      absentSupport
      Set.ofList [tagNode.Id; presentClaimId; absentClaimId; formation.Id] ]
  let choice = BoundaryOptionalEntryChoice.Conditional(selectNode.Id, tagNode.Id, whenTrueArm, whenFalseArm)
  let operand : BoundaryOperand =
    { Actual = selectNode.Id; Formal = formalParam; Abi = BoundaryScalar.Entry invocationId
      Adaptation = None; OptionalEntry = Some choice }
  let boundaryCall : BoundaryCall =
    { Site = callNode.Id; Import = importId; Resource = None; Callee = calleeLeaf.Id; Entry = None
      Arguments = [operand]; ErasedUnitArguments = []; Result = None; ResultAdaptation = None
      Participants = callParticipants; SourceTypes = Map.ofList [formalParam, optionType; selectNode.Id, optionType] }
  let callable = { preAccountGraph.Emission.Callable with AggregateDependencies = dependencies }
  { preAccountGraph with
      ObligationSources =
        Map.ofList [
          presentClaimId, [List.distinct (callNode.Id :: Set.toList presentSupport)]
          absentClaimId, [List.distinct (callNode.Id :: Set.toList absentSupport)] ]
      Codata =
        { preAccountGraph.Codata with
            CallableContracts = callable.Contracts
            CallableCarriers = callable.Carriers
            CallableFlows = callable.Flows
            CallableAggregateSlots = callable.AggregateSlots
            CallableAggregateValues = callable.AggregateValues
            CallableAggregateDependencies = callable.AggregateDependencies }
      Emission =
        { preAccountGraph.Emission with
            Callable = callable
            Boundary =
              { preAccountGraph.Emission.Boundary with
                  Imports = Map.ofList [importId, imported]
                  ByScope = Map.ofList [moduleScope.Id, [importId]]
                  CallbackInvocations = Map.ofList [invocationId, invocation]
                  ClosedEntries = Map.ofList [formation.Id, closedEntry]
                  CallbackAbsences = Map.ofList [absenceQuote, absence]
                  Calls = Map.ofList [callNode.Id, boundaryCall] } } }

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``conditional optional boundary call witnesses assigned tag projection and arm conversion citizens`` reversed =
  let graph = conditionalOptionalBoundaryFixture reversed
  let violations = Integrity.check graph
  Assert.True(violations.IsEmpty, sprintf "Expected valid conditional optional-entry revision, found: %A" violations)
  let validatedSome =
    Alex.Patterns.CallableAggregatePatterns.validateOperation
      graph (NodeId 25) graph.Nodes[NodeId 25].Kind
  Assert.True(Result.isOk validatedSome, sprintf "Expected Some construction to validate under Conditional choice: %A" validatedSome)
  let call = graph.Emission.Boundary.Calls[NodeId 30]
  let operand = call.Arguments.Head
  Assert.Equal(
    Result.Error "Optional native-entry boundary conversion requires target-pathway authority; this consumer does not admit it.",
    BoundaryAbi.optionalEntryConversionAt graph call 0 operand)
  Assert.Equal(
    Result.Error "Optional native-entry absence conversion lacks its exact current source account.",
    BoundaryAbi.optionalEntryAbsenceConversionAt graph call 0 operand)
  let accumulator = MLIRAccumulator.empty ()
  let optionCarrier = TMemRefStatic(1, TInt(IntWidth 8))
  let tagCarrier = TInt(IntWidth 64)
  MLIRAccumulator.bindNode (NodeId 27) (Arg 0) optionCarrier accumulator
  MLIRAccumulator.bindNode (NodeId 28) (V(28, 0)) tagCarrier accumulator
  match matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus graph graph.Nodes[NodeId 30]) 64 accumulator with
  | Result.Ok((operations, TRVoid), _) ->
    Assert.Equal(NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None operations)
    match operations with
    | [ FuncOp(FuncConstant(codeSSA, "Native.callback", sigType))
        OptionalEntryCall(site, [actual], [slot], results) ] ->
      let expectedSig = TFunc([TInt(IntWidth 64)], [TInt(IntWidth 64)])
      Assert.Equal(expectedSig, sigType)
      Assert.Equal(NodeId 30, site)
      Assert.Equal({ SSA = Arg 0; Type = optionCarrier }, actual)
      Assert.Equal(0, slot.Ordinal)
      Assert.Empty results
      match slot.Choice with
      | OptionalEntrySlotChoice.Conditional(selection, heldTag, heldTrue, heldFalse) ->
        Assert.Equal(NodeId 27, selection)
        Assert.Equal({ SSA = V(28, 0); Type = tagCarrier }, heldTag)
        let expectedPresent = { CaseOrdinal = 1; Claim = NodeId 720; Code = Some { SSA = codeSSA; Type = expectedSig } }
        let expectedAbsent = { CaseOrdinal = 0; Claim = NodeId 721; Code = None }
        if reversed then
          Assert.Equal(expectedAbsent, heldTrue)
          Assert.Equal(expectedPresent, heldFalse)
        else
          Assert.Equal(expectedPresent, heldTrue)
          Assert.Equal(expectedAbsent, heldFalse)
      | other -> failwithf "Expected conditional optional slot choice: %A" other
    | other -> failwithf "Unexpected witnessed operations for conditional optional boundary call: %A" other
  | other -> failwithf "Valid conditional optional boundary call was refused: %A" other

[<Theory>]
[<InlineData("missing-tag", false)>]
[<InlineData("missing-tag", true)>]
[<InlineData("wrong-tag-target", false)>]
[<InlineData("duplicate-case", false)>]
[<InlineData("shared-obligation", true)>]
[<InlineData("missing-select", false)>]
[<InlineData("missing-absence-account", true)>]
[<InlineData("unwitnessed-tag", false)>]
[<InlineData("unwitnessed-tag", true)>]
let ``conditional optional entry refuses malformed tag projection or arm conversion accounts`` defect reversed =
  let baseGraph = conditionalOptionalBoundaryFixture reversed
  Assert.Empty(Integrity.check baseGraph)
  let boundary = baseGraph.Emission.Boundary
  let call = boundary.Calls[NodeId 30]
  let operand = call.Arguments.Head
  let whenTrue, whenFalse =
    match operand.OptionalEntry with
    | Some(BoundaryOptionalEntryChoice.Conditional(_, _, t, f)) -> t, f
    | other -> failwithf "Expected conditional choice in base fixture: %A" other
  let mutateChoice choice =
    let changedOperand = { operand with OptionalEntry = Some choice }
    let changedCall = { call with Arguments = [changedOperand] }
    let changedBoundary = { boundary with Calls = boundary.Calls.Add(call.Site, changedCall) }
    { baseGraph with Emission = { baseGraph.Emission with Boundary = changedBoundary } }
  let graph =
    match defect with
    | "missing-tag" ->
      { baseGraph with Nodes = baseGraph.Nodes.Remove(NodeId 28) }
    | "wrong-tag-target" ->
      let wrongTag = { baseGraph.Nodes[NodeId 28] with Kind = SemanticKind.DUGetTag(NodeId 26, baseGraph.Nodes[NodeId 27].Type) }
      { baseGraph with Nodes = baseGraph.Nodes.Add(NodeId 28, wrongTag) }
    | "duplicate-case" ->
      let dupTrue = { whenTrue with CaseOrdinal = 1 }
      let dupFalse = { whenFalse with CaseOrdinal = 1 }
      mutateChoice (BoundaryOptionalEntryChoice.Conditional(NodeId 27, NodeId 28, dupTrue, dupFalse))
    | "shared-obligation" ->
      let sharedFalse = { whenFalse with Obligation = whenTrue.Obligation }
      mutateChoice (BoundaryOptionalEntryChoice.Conditional(NodeId 27, NodeId 28, whenTrue, sharedFalse))
    | "missing-select" ->
      let callable =
        { baseGraph.Emission.Callable with
            AggregateValues = baseGraph.Emission.Callable.AggregateValues.Remove(NodeId 27) }
      { baseGraph with Emission = { baseGraph.Emission with Callable = callable } }
    | "missing-absence-account" ->
      let changedBoundary = { boundary with CallbackAbsences = Map.empty }
      { baseGraph with Emission = { baseGraph.Emission with Boundary = changedBoundary } }
    | "unwitnessed-tag" ->
      baseGraph
    | other -> failwithf "Unknown conditional optional defect: %s" other
  let mutatedCall = graph.Emission.Boundary.Calls[NodeId 30]
  let mutatedOperand = mutatedCall.Arguments.Head
  Assert.Equal(
    Result.Error "Optional native-entry boundary conversion requires target-pathway authority; this consumer does not admit it.",
    BoundaryAbi.optionalEntryConversionAt graph mutatedCall 0 mutatedOperand)
  Assert.Equal(
    Result.Error "Optional native-entry absence conversion lacks its exact current source account.",
    BoundaryAbi.optionalEntryAbsenceConversionAt graph mutatedCall 0 mutatedOperand)
  let accumulator = MLIRAccumulator.empty ()
  if defect = "unwitnessed-tag" then
    let optionCarrier = TMemRefStatic(1, TInt(IntWidth 8))
    MLIRAccumulator.bindNode mutatedOperand.Actual (Arg 0) optionCarrier accumulator
  match matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus graph graph.Nodes[NodeId 30]) 64 accumulator with
  | Result.Error reason ->
    let expectedReason =
      if defect = "unwitnessed-tag" then
        "Conditional optional entry at boundary call 30 operand 0 has unwitnessed tag projection 28."
      else
        "Conditional optional-entry conversion at boundary call 30 operand 0 requires source-authored assigned tag projection and both arm conversions."
    Assert.Equal(expectedReason, reason)
  | Result.Ok result -> failwithf "Malformed conditional entry (%s) was lowered: %A" defect result
  Assert.Empty accumulator.AllOps
  if defect <> "unwitnessed-tag" then
    Assert.Null(MLIRAccumulator.recallNode mutatedOperand.Actual accumulator)
  Assert.Null(MLIRAccumulator.recallNode (NodeId 28) accumulator)
  Assert.Null(MLIRAccumulator.recallNode call.Site accumulator)

/// The imported operand is the declaration reference from the real source
/// shape, including its uncommitted integer formal. Only the native descriptor
/// commits an ABI; it does not create an ordinary closure's physical signature.
let private importedDeclarationOperandFixture () =
    let graph = importedFixture ()
    let sourceSignature = functionFrom intType intType

    let pointerType =
        TypeIdentity.Application(
            {
                Declaration = { Module = []; Name = "FnPtr" }
                Parameters = [ TypeParamKind.Type ]
                NativeKind = Some NTUKind.NTUfnptr
            },
            [ sourceSignature ]
        )

    let sourceNodes =
        [
            node 882 (SemanticKind.PatternBinding "count") intType [] (Some 884)
            node
                883
                (SemanticKind.Literal(NativeLiteral.Int(0L, NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register))))
                intType
                []
                (Some 884)
            node
                884
                (SemanticKind.Lambda([ "count", intType, NodeId 882 ], NodeId 883, [], None, LambdaContext.RegularClosure))
                sourceSignature
                [ 882; 883 ]
                (Some 30)
            node 30 (SemanticKind.Binding("fixture_extern", false, false, None)) sourceSignature [ 884 ] (Some 35)
            node
                925
                (SemanticKind.Intrinsic
                    {
                        Module = IntrinsicModule.FnPtr
                        Operation = "ofExtern"
                        Category = IntrinsicCategory.Pure
                        FullName = "FnPtr.ofExtern"
                    })
                (functionFrom sourceSignature pointerType)
                []
                (Some 31)
            node 926 (SemanticKind.VarRef("fixture_extern", Some(NodeId 30))) sourceSignature [] (Some 31)
            node 31 (SemanticKind.Application(NodeId 925, [ NodeId 926 ])) pointerType [ 925; 926 ] (Some 32)
            node 32 (SemanticKind.Binding("entry", false, false, None)) pointerType [ 31 ] (Some 35)
            node 35 (SemanticKind.Sequential [ NodeId 32 ]) pointerType [ 32 ] None
        ]

    let imported = graph.Emission.Boundary.Imports[NodeId 44]

    let imported =
        { imported with
            Parameters = [ NodeId 882, BoundaryScalar.Integer(64, true) ]
            Result = Some(BoundaryScalar.Integer(64, true))
        }

    let entry = graph.Emission.Boundary.Entries[NodeId 31]

    let entry =
        { entry with
            Operand = NodeId 926
            SourceType = pointerType
            Transport = Set.ofList [ NodeId 30; NodeId 31; NodeId 925; NodeId 926 ]
        }

    let sourceCarrier =
        {
            Occurrence = NodeId 926
            SourceType = sourceSignature
            Implementation = NodeId 884
            Kind = CallableKind.OrdinaryFlatClosure
            Formation = NodeId 884
            EnvironmentValue = None
            Contract = Ok(NodeId 884)
            Lifetime = []
            Parameters = [ "count", intType, NodeId 882 ]
            ParameterShapes = [ CallableValueShape.Data(NodeId 882) ]
            OmittedParameters = Set.empty
            Result = NodeId 883
            ResultShape = CallableValueShape.Data(NodeId 883)
            Environment = None
        }

    let sourceDeclaration =
        {
            Lookup = NodeId 884
            Implementation = NodeId 884
            Parameters = sourceCarrier.Parameters
            Result = NodeId 883
            Context = LambdaContext.RegularClosure
            Captures = []
            Name = CallableSymbolName.LocalBinding(NodeId 30, "fixture_extern")
            Parent = Some(NodeId 30)
            Participants = Set.ofList [ NodeId 30; NodeId 882; NodeId 883; NodeId 884 ]
        }

    { graph with
        Nodes = sourceNodes |> List.map (fun n -> n.Id, n) |> Map.ofList
        Emission =
            { graph.Emission with
                Boundary =
                    { graph.Emission.Boundary with
                        Imports = Map.ofList [ imported.Identity, imported ]
                        Entries = Map.ofList [ entry.Formation, entry ]
                        Calls = Map.empty
                    }
                Callable =
                    { graph.Emission.Callable with
                        Carriers = Map.ofList [ NodeId 926, sourceCarrier ]
                        DefinitionOnlyBindings = Set.singleton (NodeId 30)
                        Declarations = Map.ofList [ NodeId 884, sourceDeclaration; NodeId 30, { sourceDeclaration with Lookup = NodeId 30; Parent = Some(NodeId 35) } ]
                        SignatureData = Map.ofList [ NodeId 884, Set.ofList [ NodeId 882; NodeId 883 ] ]
                        ValueShapes =
                            sourceNodes
                            |> List.map (fun n ->
                                n.Id,
                                if n.Id = NodeId 926 then
                                    CallableValueShape.Callable n.Id
                                else
                                    CallableValueShape.Data n.Id)
                            |> Map.ofList
                        AliasTargets = sourceNodes |> List.map (fun n -> n.Id, n.Id) |> Map.ofList
                        ClosedData = Set.ofList [ NodeId 882; NodeId 883 ]
                    }
                Numeric =
                    { graph.Emission.Numeric with
                        OccurrenceRepresentations = Map.ofList [ NodeId 882, Result.Error "requires an exact settled value occurrence" ]
                    }
            }
    }
    |> declareBindingReadings

/// Direct scalar invocation reuses the imported declaration's native signature.
/// These contract rows state both adaptations; they perform no source inference.
let private scalarBoundaryFixture () =
  let graph = importedDeclarationOperandFixture ()
  let site, actual = NodeId 929, NodeId 927
  let argumentMeet = {Consumer=site;Operand=actual;From=8;To=64;Adapt=MeetKind.ExtendUnsigned}
  let resultMeet = {Consumer=site;Operand=site;From=64;To=8;Adapt=MeetKind.Truncate}
  let imported = graph.Emission.Boundary.Imports[NodeId 44]
  let call : BoundaryCall =
    {Site=site;Import=imported.Identity;Callee=NodeId 928;Entry=None;Resource=None
     Arguments=[{Actual=actual;Formal=NodeId 882;Abi=BoundaryScalar.Integer(64,true);Adaptation=Some argumentMeet;OptionalEntry=None}]
     ErasedUnitArguments=[];Result=imported.Result;ResultAdaptation=Some resultMeet
     Participants=Set.empty;SourceTypes=Map.empty}
  let nodes =
    [node 927 (SemanticKind.PatternBinding "argument") intType [] (Some 929)
     node 928 (SemanticKind.VarRef("fixture_extern",Some(NodeId 30))) (functionFrom intType intType) [] (Some 929)
     node 929 (SemanticKind.Application(NodeId 928,[actual])) intType [928;927] (Some 35)]
  let owner = graph.Nodes[NodeId 35]
  let nodes =
    nodes |> List.fold(fun held value -> Map.add value.Id value held)
      (graph.Nodes.Add(owner.Id,{owner with Kind=SemanticKind.Sequential[NodeId 32;site];Children=[NodeId 32;site];Type=intType}))
  let boundary = {graph.Emission.Boundary with Calls=Map.ofList[site,call]}
  let aliases = [NodeId 927;NodeId 928;site] |> List.fold(fun held id -> Map.add id id held) graph.Emission.Callable.AliasTargets
  let callable = {graph.Emission.Callable with AliasTargets=aliases}
  {graph with
    Nodes=nodes
    Codata={graph.Codata with Meets=graph.Codata.Meets.Add(site,[argumentMeet;resultMeet])}
    Emission={graph.Emission with Boundary=boundary;Callable=callable}}
  |> declareBindingReadings

[<Fact>]
let ``direct scalar boundary preserves native call between published argument and result adaptations`` () =
  let graph = scalarBoundaryFixture ()
  let operands = MLIRAccumulator.empty ()
  MLIRAccumulator.bindNode (NodeId 927) (Arg 0) (TInt(IntWidth 8)) operands
  match matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus graph graph.Nodes[NodeId 929]) 64 operands with
  | Result.Ok((operations,TRValue result),_) ->
    match operations with
    | [ArithOp(ArithOp.ExtUI(argument,Arg 0,argumentFrom,argumentTo));
       FuncOp(FuncCall([native],"fixture_extern",[actual]));
       ArithOp(ArithOp.TruncI(adapted,source,resultFrom,resultTo))] ->
      Assert.Equal(TInt(IntWidth 8),argumentFrom)
      Assert.Equal(TInt(IntWidth 64),argumentTo)
      Assert.Equal({SSA=argument;Type=argumentTo},actual)
      Assert.Equal(TInt(IntWidth 64),native.Type)
      Assert.Equal(native.SSA,source)
      Assert.Equal(TInt(IntWidth 64),resultFrom)
      Assert.Equal(TInt(IntWidth 8),resultTo)
      Assert.Equal({SSA=adapted;Type=resultTo},result)
    | other -> failwithf "Direct scalar boundary lost its ordered native invocation or source adaptations: %A" other
  | other -> failwithf "Direct scalar boundary did not produce its narrowed source result: %A" other
  Assert.Empty operands.AllOps
  Assert.Null(MLIRAccumulator.recallNode (NodeId 929) operands)
  Assert.Equal(Some(Arg 0,TInt(IntWidth 8)),MLIRAccumulator.recallNode (NodeId 927) operands)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``direct scalar boundary refuses withdrawn current argument or result adaptation`` resultMeet =
  let graph = scalarBoundaryFixture ()
  let withdrawn = if resultMeet then NodeId 929 else NodeId 927
  let meets = graph.Codata.Meets[NodeId 929] |> List.filter(fun meet -> meet.Operand<>withdrawn)
  let graph =
    {graph with Codata={graph.Codata with Meets=graph.Codata.Meets.Add(NodeId 929,meets)}}
  let operands = MLIRAccumulator.empty ()
  MLIRAccumulator.bindNode (NodeId 927) (Arg 0) (TInt(IntWidth 8)) operands
  match matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus graph graph.Nodes[NodeId 929]) 64 operands with
  | Result.Error reason -> Assert.Equal("Published adaptation disagrees with its exact source numeric meet.",reason)
  | other -> failwithf "Direct scalar boundary admitted a withdrawn current adaptation: %A" other
  Assert.Empty operands.AllOps
  Assert.Null(MLIRAccumulator.recallNode (NodeId 929) operands)
  Assert.Equal(Some(Arg 0,TInt(IntWidth 8)),MLIRAccumulator.recallNode (NodeId 927) operands)

[<Fact>]
let ``imported declaration operand needs no ordinary formal representation or runtime SSA`` () =
    let graph = importedDeclarationOperandFixture ()
    let accumulator = MLIRAccumulator.empty ()
    let zipper = at graph 35 [ 32; 31; 926 ]

    let ctx =
        { context graph (NodeId 35) accumulator with
            Zipper = zipper
        }

    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx zipper.Focus
    Assert.Equal(TRVoid, output.Result)
    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Null(MLIRAccumulator.recallNode (NodeId 926) accumulator)
    Assert.True(graph.Emission.Numeric.OccurrenceRepresentations[NodeId 882] |> Result.isError)
    let formation = at graph 35 [ 32; 31 ]

    let output =
        Alex.Witnesses.FunctionPointerWitness.nanopass.Witness { ctx with Zipper = formation } formation.Focus

    match output.Result, output.InlineOps with
    | TRValue value, [ FuncOp(FuncConstant(_, "fixture_extern", ty)) ] ->
        Assert.Equal(TFunc([ TInt(IntWidth 64) ], [ TInt(IntWidth 64) ]), ty)
        Assert.Equal(ty, value.Type)
    | other -> failwithf "Native ABI address formation was not transcribed: %A" other

[<Fact>]
let ``ordinary callable reference still refuses an unresolved declaration formal`` () =
    let graph = importedDeclarationOperandFixture ()

    let graph =
        { graph with
            Nodes =
                graph.Nodes.Add(
                    NodeId 35,
                    { graph.Nodes[NodeId 35] with
                        Kind = SemanticKind.Sequential[NodeId 926]
                        Children = [ NodeId 926 ]
                    }
                )
        }
        |> declareTraversalReadings

    let accumulator = MLIRAccumulator.empty ()
    let zipper = at graph 35 [ 926 ]

    let ctx =
        { context graph (NodeId 35) accumulator with
            Zipper = zipper
        }

    let output = Alex.Witnesses.VarRefWitness.nanopass.Witness ctx zipper.Focus

    match output.Result with
    | TRError diagnostic ->
        Assert.Contains(
            "Callable signature data participant 882 has an unresolved source-published physical representation",
            diagnostic.Message
        )
    | other -> failwithf "Ordinary callable gained native-declaration metadata authority: %A" other

    Assert.Empty output.InlineOps
    Assert.Empty output.TopLevelOps
    Assert.Null(MLIRAccumulator.recallNode (NodeId 926) accumulator)

[<Fact>]
let ``imported call refuses an unwitnessed pointer child instead of rematerializing its symbol`` () =
    let graph = importedFixture ()

    let graph =
        { graph with
            Nodes =
                graph.Nodes.Add(
                    NodeId 34,
                    { graph.Nodes[NodeId 34] with
                        Children = []
                    }
                )
        }
        |> declareTraversalReadings

    let ctx = importedTraversal graph
    Assert.True(ctx.Accumulator.Errors |> List.exists (fun d -> d.Message.Contains("33")))
    Assert.Null(MLIRAccumulator.recallNode (NodeId 33) ctx.Accumulator)
    Assert.Single(ScopeContext.getOps ctx.ScopeContext.Value) |> ignore

[<Theory>]
[<InlineData("loading", "Imported entry has no current source-published loading assumption.")>]
[<InlineData("declaration", "Imported entry no longer has its exact declaration, import and loading contract.")>]
[<InlineData("transport", "Imported invocation differs from its source entry and pointer transport.")>]
[<InlineData("signature", "Imported invocation pointer and operands disagree with its native ABI.")>]
let ``imported invocation refuses its missing source account or wrong physical operand`` defect reason =
    let graph = importedFixture ()
    let entry = graph.Emission.Boundary.Entries[NodeId 31]

    let boundary =
        match defect with
        | "loading" ->
            { graph.Emission.Boundary with
                Loading = None
            }
        | "declaration" ->
            { graph.Emission.Boundary with
                Entries = Map.ofList [ entry.Formation, { entry with Declaration = NodeId 32 } ]
            }
        | "transport" ->
            { graph.Emission.Boundary with
                Entries =
                    Map.ofList
                        [
                            entry.Formation,
                            { entry with
                                Transport = Set.remove (NodeId 33) entry.Transport
                            }
                        ]
            }
        | _ -> graph.Emission.Boundary

    let graph =
        { graph with
            Emission =
                { graph.Emission with
                    Boundary = boundary
                }
        }

    let operands = MLIRAccumulator.empty ()
    let pointerType = if defect = "signature" then TIndex else TFunc([], [])
    MLIRAccumulator.bindNode (NodeId 33) (Arg 0) pointerType operands
    let ctx = context graph (NodeId 34) operands

    match
        Alex.XParsec.PSGCombinators.tryMatchWithDiagnostics
            Alex.Patterns.PlatformPatterns.pBoundaryCall
            graph
            graph.Nodes[NodeId 34]
            ctx.Zipper
            ctx.Coeffects
            operands
    with
    | Result.Error actual -> Assert.Equal(reason, actual)
    | Result.Ok actual -> failwithf "Changed imported invocation was witnessed: %A" actual

/// Component representation controls only. Actual source resource declaration,
/// conversion and cleanup admission are separate published-graph gates.
[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``opaque resource Option retains its exact source case order and placement`` reversed =
    let handle = ValueRepresentation.Scalar(SettledSlot.CHandle(unitType, 64, 4))
    let cases = ["absent", []; "present", [handle]]
    let representation = ValueRepresentation.Union((if reversed then List.rev cases else cases), Some(4, 12, 4))
    let actual = Alex.CodeGeneration.TypeMapping.representationType representation
    Assert.Equal(TResourceOption representation, actual)
    Assert.Equal(Some(TOpaqueHandle(unitType, 64, 4)), SettledScalar.tryType (SettledSlot.CHandle(unitType, 64, 4)))
    Assert.Equal(NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [ResourceAlias(NodeId 1, {SSA=Arg 0;Type=actual})])

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``resource ABI cannot become a generic imported or callable scalar`` nullable =
    let error = Assert.Throws<System.ArgumentException>(fun () ->
        BoundaryAbi.scalarType (BoundaryScalar.ResourceHandle(NodeId 1, nullable)) |> ignore)
    Assert.Contains("requires its exact direct-call conversion and cleanup accounts", error.Message)

/// This deliberately incomplete component fixture has no resource declaration
/// or proof bodies either: the asserted gate is the missing per-call account,
/// not a claim that the whole revision would otherwise be admitted.
[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``resource boundary refuses a missing per-call conversion and cleanup account`` nullable =
    let graph = importedFixture ()
    let boundary = graph.Emission.Boundary
    let call = boundary.Calls[NodeId 34]
    let imported = boundary.Imports[call.Import]
    let scalar = BoundaryScalar.ResourceHandle(NodeId 70, nullable)
    let imported =
        if nullable then {imported with Result=Some scalar}
        else {imported with Parameters=[NodeId 71,scalar];Result=None}
    let graph =
        { graph with
            Emission =
                { graph.Emission with
                    Boundary =
                        { boundary with
                            Imports = boundary.Imports.Add(imported.Identity, imported)
                            Calls = boundary.Calls.Add(call.Site, {call with Entry=None;Resource=None}) } } }
    let accumulator = MLIRAccumulator.empty ()
    let ctx = context graph call.Site accumulator
    match Alex.XParsec.PSGCombinators.tryMatchWithDiagnostics
            Alex.Patterns.PlatformPatterns.pBoundaryCall graph graph.Nodes[call.Site]
            ctx.Zipper ctx.Coeffects accumulator with
    | Result.Error reason -> Assert.Equal("Resource call lacks its source conversion and cleanup account.", reason)
    | Result.Ok _ -> failwith "Resource boundary emitted without a per-call conversion/cleanup account."
    Assert.Null(MLIRAccumulator.recallNode call.Site accumulator)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``opaque resource carriers do not acquire generic spatial storage authority`` option =
    let handle = ValueRepresentation.Scalar(SettledSlot.CHandle(unitType, 64, 8))
    let carrier = if option then TResourceOption(ValueRepresentation.Union(["absent", []; "present", [handle]], Some(8,16,8))) else TOpaqueHandle(unitType,64,8)
    let error = Assert.Throws<System.Exception>(fun () -> mlirTypeSizeWith (Ok 64) carrier |> ignore)
    Assert.Contains("opaque resource cannot acquire generic spatial storage authority", error.Message)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``resource Option refuses missing placement or an extra opaque alternative`` extra =
    let handle = ValueRepresentation.Scalar(SettledSlot.CHandle(unitType, 64, 8))
    let cases = ["absent", []; "present", [handle]] @ (if extra then ["other", [handle]] else [])
    let representation = ValueRepresentation.Union(cases, if extra then Some(8,16,8) else None)
    let error = Assert.Throws<System.Exception>(fun () -> Alex.CodeGeneration.TypeMapping.representationType representation |> ignore)
    Assert.Contains("requires its complete source-settled case and byte placement", error.Message)
