module Alex.Tests.MutableClosureTests

open System.Diagnostics
open System.IO
open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper
module Operands = Alex.Traversal.CallableOperands

let private boolean = TInt(IntWidth 1)
let private unitType = TInt(IntWidth 32)
let private codeType = TFunc([unitType], [boolean])
let private ok = function Result.Ok value -> value | Result.Error reason -> failwith reason

/// These component events have already been demanded. The fixture establishes
/// neither eager source evaluation policy nor a source allocation lifetime proof.
type private Fixture = {
    Graph: Revision
    Root: Zipper.PSGZipper
    Initial: NodeId
    Replacement: NodeId
    Cell: NodeId
    FirstRead: NodeId
    Snapshot: NodeId
    Assignment: NodeId
    Target: NodeId
    LatestRead: NodeId
    SnapshotRead: NodeId
    ImmutableFunction: NodeId
}

// The revision states the nineteen nodes of the fixture, the relations their kinds imply,
// the carrier, join, storage and escape rows, the callable projection of those nodes and
// the representation of each occurrence. The fixture sets no parent.
let private fixture () =
    let unitIdentity = Alex.Tests.Build.unitType
    let functionType = functionFrom unitIdentity boolType
    // One named function is five nodes in creation order: parameter, body, code, declaration, reference.
    let named name value number =
        let parameter = node number (SemanticKind.PatternBinding "_") unitIdentity [] None
        let body = node (number + 1) (SemanticKind.Literal(NativeLiteral.Bool value)) boolType [] None
        let code =
            node (number + 2)
                 (SemanticKind.Lambda(["_", unitIdentity, parameter.Id], body.Id, [], None, LambdaContext.RegularClosure))
                 functionType [number; number + 1] None
        let declaration = node (number + 3) (SemanticKind.Binding(name, false, false, None)) functionType [number + 2] None
        let reference = node (number + 4) (SemanticKind.VarRef(name, Some declaration.Id)) functionType [] None
        [parameter; body; code; declaration; reference], declaration, reference
    let firstNodes, firstCode, initial = named "initial_code" false 0
    let secondNodes, secondCode, replacement = named "replacement_code" true 5
    let cell = node 10 (SemanticKind.Binding("selectedThunk", true, false, None)) functionType [4] None
    let firstRead = node 11 (SemanticKind.VarRef("selectedThunk", Some cell.Id)) functionType [] None
    let snapshot = node 12 (SemanticKind.Binding("snapshot", false, false, None)) functionType [11] None
    let target = node 13 (SemanticKind.VarRef("selectedThunk", Some cell.Id)) functionType [] None
    let assignment = node 14 (SemanticKind.Set(target.Id, replacement.Id)) Alex.Tests.Build.unitType [13; 9] None
    let latestRead = node 15 (SemanticKind.VarRef("selectedThunk", Some cell.Id)) functionType [] None
    let snapshotRead = node 16 (SemanticKind.VarRef("snapshot", Some snapshot.Id)) functionType [] None
    let immutableFunction = node 17 (SemanticKind.Binding("unchanged", false, false, None)) functionType [4] None
    let root =
        node 18 (SemanticKind.Sequential
                    [firstCode.Id; secondCode.Id; cell.Id; snapshot.Id; assignment.Id
                     latestRead.Id; snapshotRead.Id; immutableFunction.Id])
             functionType [3; 8; 10; 12; 14; 15; 16; 17] None
    let edge sources target relation role ordinal : Hyperedge =
        { Sources = List.map NodeId sources; Target = NodeId target; Class = relation; Role = role; Ordinal = ordinal }
    // The relations the node kinds imply, in node order.
    let kindEdges =
        [edge [0] 2 EdgeClass.Structural EdgeRole.Parameter 0
         edge [1] 2 EdgeClass.Structural EdgeRole.Body 0
         edge [2] 3 EdgeClass.Structural EdgeRole.Attached 0
         edge [3] 4 EdgeClass.Reference EdgeRole.Definition 0
         edge [5] 7 EdgeClass.Structural EdgeRole.Parameter 0
         edge [6] 7 EdgeClass.Structural EdgeRole.Body 0
         edge [7] 8 EdgeClass.Structural EdgeRole.Attached 0
         edge [8] 9 EdgeClass.Reference EdgeRole.Definition 0
         edge [4] 10 EdgeClass.Structural EdgeRole.Attached 0
         edge [10] 11 EdgeClass.Reference EdgeRole.Definition 0
         edge [11] 12 EdgeClass.Structural EdgeRole.Attached 0
         edge [10] 13 EdgeClass.Reference EdgeRole.Definition 0
         edge [13] 14 EdgeClass.Structural EdgeRole.AssignTarget 0
         edge [9] 14 EdgeClass.Structural EdgeRole.AssignValue 0
         edge [10] 15 EdgeClass.Reference EdgeRole.Definition 0
         edge [12] 16 EdgeClass.Reference EdgeRole.Definition 0
         edge [4] 17 EdgeClass.Structural EdgeRole.Attached 0
         edge [3] 18 EdgeClass.Structural EdgeRole.Element 0
         edge [8] 18 EdgeClass.Structural EdgeRole.Element 1
         edge [10] 18 EdgeClass.Structural EdgeRole.Element 2
         edge [12] 18 EdgeClass.Structural EdgeRole.Element 3
         edge [14] 18 EdgeClass.Structural EdgeRole.Element 4
         edge [15] 18 EdgeClass.Structural EdgeRole.Element 5
         edge [16] 18 EdgeClass.Structural EdgeRole.Element 6
         edge [17] 18 EdgeClass.Structural EdgeRole.Element 7]
    let ids numbers = numbers |> List.map NodeId |> Set.ofList
    let keyed rows = rows |> List.map (fun (number, row) -> NodeId number, row) |> Map.ofList
    let carrier occurrence implementation formal result : CallableCarrier =
        { Occurrence = NodeId occurrence; SourceType = functionType; Implementation = NodeId implementation
          Parameters = ["_", unitIdentity, NodeId formal]
          ParameterShapes = [CallableValueShape.Data (NodeId formal)]
          OmittedParameters = Set.empty
          Result = NodeId result; ResultShape = CallableValueShape.Data (NodeId result)
          Environment = None }
    let carriers =
        keyed [2, carrier 2 2 0 1; 3, carrier 3 2 0 1; 4, carrier 4 2 0 1
               7, carrier 7 7 5 6; 8, carrier 8 7 5 6; 9, carrier 9 7 5 6
               17, carrier 17 2 0 1; 18, carrier 18 2 0 1]
    let join occurrence read : CallableJoin =
        { Occurrence = NodeId occurrence; SourceType = functionType; Storage = cell.Id; Read = NodeId read
          Alternatives = [initial.Id; replacement.Id] }
    let joins = keyed [11, join 11 11; 12, join 12 11; 15, join 15 15; 16, join 16 11]
    let storage: MutableCallableStorage =
        { Binding = cell.Id; SourceType = functionType
          Initializer = { Site = cell.Id; Destination = cell.Id; Value = initial.Id; Alternative = 0 }
          Writes = [{ Site = assignment.Id; Destination = target.Id; Value = replacement.Id; Alternative = 1 }]
          Reads = Set.ofList [firstRead.Id; latestRead.Id]
          Alternatives = [initial.Id; replacement.Id]
          AlternativeCarriers = [carriers[initial.Id]; carriers[replacement.Id]]
          EnvironmentBytes = None; Captures = Set.empty; Borrows = Set.empty }
    let declaration lookup implementation formal result name participants : CallableEmissionDeclaration =
        { Lookup = NodeId lookup; Implementation = NodeId implementation
          Parameters = ["_", unitIdentity, NodeId formal]; Result = NodeId result
          Context = LambdaContext.RegularClosure; Captures = []; Name = name; Parent = None
          Participants = ids participants }
    let data number = number, CallableValueShape.Data (NodeId number)
    let callable number = number, CallableValueShape.Callable (NodeId number)
    let callables: CallableEmissionProjection =
        { Empty.callable with
            Carriers = carriers
            Joins = joins
            MutableStorage = Map.ofList [cell.Id, storage]
            ValueShapes =
                keyed [data 0; data 1; callable 2; callable 3; callable 4
                       data 5; data 6; callable 7; callable 8; callable 9
                       callable 10; callable 11; callable 12; callable 13; data 14
                       callable 15; callable 16; callable 17; callable 18]
            SignatureData = keyed [2, Set.empty; 7, Set.empty]
            Transports =
                keyed [2, ids [2]; 3, ids [2; 3]; 4, ids [2; 3; 4]
                       7, ids [7]; 8, ids [7; 8]; 9, ids [7; 8; 9]
                       11, ids [10; 11]; 12, ids [10; 11; 12]; 15, ids [10; 15]; 16, ids [10; 11; 12; 16]
                       17, ids [2; 3; 4; 17]; 18, ids [2; 3; 4; 17; 18]]
            Declarations =
                keyed [2, declaration 2 2 0 1 (CallableSymbolName.Anonymous (NodeId 2)) [0; 1; 2]
                       3, declaration 3 2 0 1 (CallableSymbolName.RootBinding "initial_code") [0; 1; 2; 3]
                       7, declaration 7 7 5 6 (CallableSymbolName.Anonymous (NodeId 7)) [5; 6; 7]
                       8, declaration 8 7 5 6 (CallableSymbolName.RootBinding "replacement_code") [5; 6; 7; 8]]
            Symbols =
                keyed [2, CallableSymbolName.Anonymous (NodeId 2)
                       3, CallableSymbolName.RootBinding "initial_code"
                       7, CallableSymbolName.Anonymous (NodeId 7)
                       8, CallableSymbolName.RootBinding "replacement_code"
                       10, CallableSymbolName.RootBinding "selectedThunk"
                       12, CallableSymbolName.RootBinding "snapshot"
                       17, CallableSymbolName.RootBinding "unchanged"]
            DirectCallees = keyed [4, NodeId 3; 9, NodeId 8]
            MutableRetentions = ids [4; 9]
            FunctionBindings = ids [3; 8]
            DefinitionOnlyBindings = ids [3; 8]
            Arguments = keyed [2, keyed [0, [0]]; 7, keyed [5, [0]]]
            AliasTargets =
                keyed [0, NodeId 0; 1, NodeId 1; 2, NodeId 2; 3, NodeId 2; 4, NodeId 2
                       5, NodeId 5; 6, NodeId 6; 7, NodeId 7; 8, NodeId 7; 9, NodeId 7
                       10, NodeId 10; 11, NodeId 11; 12, NodeId 11; 13, NodeId 13; 14, NodeId 14
                       15, NodeId 15; 16, NodeId 11; 17, NodeId 2; 18, NodeId 18]
            UnitNodes = ids [0; 5; 14]
            ClosedData = ids [0; 1; 5; 6; 14]
            Supports =
                keyed [0, ids [0]; 1, ids [1]; 2, ids [0; 1; 2]; 3, ids [0; 1; 2; 3]; 4, ids [2; 3; 4]
                       5, ids [5]; 6, ids [6]; 7, ids [5; 6; 7]; 8, ids [5; 6; 7; 8]; 9, ids [7; 8; 9]
                       10, ids [10]; 11, ids [10; 11]; 12, ids [10; 11; 12]; 13, ids [13]; 14, ids [14]
                       15, ids [10; 15]; 16, ids [10; 11; 12; 16]
                       17, ids [2; 3; 4; 17]; 18, ids [2; 3; 4; 17; 18]] }
    let scalar slot : Result<ValueRepresentation, string> = Result.Ok (ValueRepresentation.Scalar slot)
    let pair : Result<ValueRepresentation, string> =
        Result.Error "Callable values require their separately published code and environment components."
    let representations =
        keyed [0, scalar SettledSlot.Unit; 1, scalar SettledSlot.Bool; 2, pair; 3, pair; 4, pair
               5, scalar SettledSlot.Unit; 6, scalar SettledSlot.Bool; 7, pair; 8, pair; 9, pair
               10, pair; 11, pair; 12, pair; 13, pair; 14, scalar SettledSlot.Unit
               15, pair; 16, pair; 17, pair; 18, pair]
    let stated =
        revision (firstNodes @ secondNodes @
                  [cell; firstRead; snapshot; target; assignment; latestRead; snapshotRead; immutableFunction; root])
    let graph =
        { stated with
            Edges = kindEdges
            Codata =
                { stated.Codata with
                    CallableCarriers = carriers
                    CallableJoins = joins
                    MutableCallableStorage = Map.ofList [cell.Id, storage]
                    Escapes = Map.ofList [cell.Id, EscapeKind.StackScoped] }
            Emission =
                { stated.Emission with
                    Callable = callables
                    Numeric = { stated.Emission.Numeric with OccurrenceRepresentations = representations } } }
    let graph = declareBindingReadings graph
    { Graph = graph; Root = Zipper.create graph root.Id |> require "Missing component root"
      Initial = initial.Id; Replacement = replacement.Id; Cell = cell.Id; FirstRead = firstRead.Id
      Snapshot = snapshot.Id; Assignment = assignment.Id; Target = target.Id; LatestRead = latestRead.Id
      SnapshotRead = snapshotRead.Id; ImmutableFunction = immutableFunction.Id }

let private context (position: Zipper.PSGZipper) pointerBits operands =
    let rootScope = ref (ScopeContext.root ())
    let scope = ref (ScopeContext.createChild rootScope.Value FunctionLevel)
    let visited = ref Set.empty
    { Coeffects = coeffects pointerBits; Accumulator = operands; RootAccumulator = operands
      ScopeContext = scope; RootScopeContext = rootScope; Graph = position.Graph; Zipper = position
      GlobalVisited = visited; TraversalVisited = visited }

let private inputValue id = { SSA = Alex.Traversal.Values.callableCode id; Type = codeType }

let private inputs fixture =
    let operands = MLIRAccumulator.empty ()
    // Initial is also shared by the unchanged binding. State the exact cell
    // initializer and assignment-value occurrences, rather than choose a path.
    for id, path in
        [ fixture.Initial, [fixture.Cell; fixture.Initial]
          fixture.Replacement, [fixture.Assignment; fixture.Replacement] ] do
        let position = path |> List.fold (fun position child -> atChild child position) fixture.Root
        Operands.bind (context position 64 operands) id (inputValue id) None |> ok
    operands

/// One public witness at its actual Huet position. No traversal, elaboration,
/// cell selection, or source demand rule is reproduced by the harness.
let private observe (nanopass: Nanopass) position pointerBits operands =
    let ctx = context position pointerBits operands
    let nodes, edges, codata = position.Graph.Nodes, position.Graph.Edges, position.Graph.Codata
    let scalars, callables, cells = operands.NodeAssoc, operands.CallableAssoc, operands.CallableCellAssoc
    let output = nanopass.Witness ctx position.Focus
    Assert.Same(position.Graph, ctx.Graph)
    Assert.Same(nodes, ctx.Graph.Nodes)
    Assert.Same(edges, ctx.Graph.Edges)
    Assert.Same(codata, ctx.Graph.Codata)
    Assert.Same(scalars, operands.NodeAssoc)
    Assert.Same(callables, operands.CallableAssoc)
    Assert.Same(cells, operands.CallableCellAssoc)
    Assert.Empty(ctx.GlobalVisited.Value)
    Assert.Empty(ctx.ScopeContext.Value.Operations)
    Assert.Empty(ctx.RootScopeContext.Value.Operations)
    Assert.Empty(operands.AllOps)
    Assert.Empty(output.TopLevelOps)
    output

let private callable output =
    match output.Result with TRCallable value -> value | other -> failwithf "Expected callable operands, got %A" other

let private remember id output operands =
    let value = callable output
    MLIRAccumulator.bindCallable id value operands |> ok
    value

let private stages pointerBits =
    let f = fixture ()
    let operands = inputs f
    let binding = observe Alex.Witnesses.BindingWitness.nanopass (f.Root |> atChild f.Cell) pointerBits operands
    let cell =
        match binding.Result with
        | TRCallableCell cell -> MLIRAccumulator.bindCallableCell f.Cell cell operands |> ok; cell
        | other -> failwithf "Expected admitted callable storage, got %A" other
    Assert.Equal(TMemRefStatic(1, TIndex), (Operands.cellDiscriminator cell).Type)
    Assert.Equal(None, Operands.cellEnvironment cell)
    let firstRead = observe Alex.Witnesses.VarRefWitness.nanopass
                        (f.Root |> atChild f.Snapshot |> atChild f.FirstRead) pointerBits operands
    let before = remember f.FirstRead firstRead operands
    let snapshot = observe Alex.Witnesses.BindingWitness.nanopass (f.Root |> atChild f.Snapshot) pointerBits operands
    let saved = remember f.Snapshot snapshot operands
    Assert.Equal(Operands.code before, Operands.code saved)
    Assert.Empty(snapshot.InlineOps)
    let destination = observe Alex.Witnesses.VarRefWitness.nanopass
                          (f.Root |> atChild f.Assignment |> atChild f.Target) pointerBits operands
    Assert.True(match destination.Result with TRVoid -> true | _ -> false)
    Assert.Empty(destination.InlineOps)
    let assignment = observe Alex.Witnesses.MutableAssignmentWitness.nanopass (f.Root |> atChild f.Assignment) pointerBits operands
    Assert.True(match assignment.Result with TRVoid -> true | _ -> false)
    let latestRead = observe Alex.Witnesses.VarRefWitness.nanopass (f.Root |> atChild f.LatestRead) pointerBits operands
    let after = callable latestRead
    let snapshotRead = observe Alex.Witnesses.VarRefWitness.nanopass (f.Root |> atChild f.SnapshotRead) pointerBits operands
    Assert.Equal(Operands.code before, Operands.code (callable snapshotRead))
    Assert.Empty(snapshotRead.InlineOps)
    Assert.NotEqual((Operands.code before).SSA, (Operands.code after).SSA)
    Assert.Equal(codeType, (Operands.code before).Type)
    Assert.Equal(codeType, (Operands.code after).Type)
    Assert.Empty(operands.Errors)
    f, operands, cell, before, after, [binding; firstRead; snapshot; assignment; latestRead; snapshotRead]

[<Fact>]
let ``mutable function reassignment targets its cell and leaves a value snapshot intact`` () =
    let f, _, cell, before, after, outputs = stages 64
    let discriminator = Operands.cellDiscriminator cell
    let operations = outputs |> List.collect _.InlineOps
    let allocations = operations |> List.choose (function MLIROp.MemRefOp(MemRefOp.Alloca(ssa, ty, _)) -> Some(ssa, ty) | _ -> None)
    Assert.Equal((discriminator.SSA, TMemRefStatic(1, TIndex)), Assert.Single allocations)
    let stores = operations |> List.choose (function MLIROp.MemRefOp(MemRefOp.Store(value, destination, _, ty, _)) -> Some(value, destination, ty) | _ -> None)
    Assert.Equal<(SSA * SSA * MLIRType) list>(
        [Alex.Traversal.Values.value f.Cell 3, discriminator.SSA, TIndex
         Alex.Traversal.Values.value f.Assignment 3, discriminator.SSA, TIndex], stores)
    let loads = operations |> List.choose (function MLIROp.MemRefOp(MemRefOp.Load(_, source, _, ty, _)) -> Some(source, ty) | _ -> None)
    Assert.Equal<(SSA * MLIRType) list>([discriminator.SSA, TIndex; discriminator.SSA, TIndex], loads)
    let switches = operations |> List.choose (function MLIROp.SCFOp(SCFOp.IndexSwitch(_, _, _, results)) -> Some results | _ -> None)
    Assert.Equal<(SSA * MLIRType) list list>([[(Operands.code before).SSA, codeType]; [(Operands.code after).SSA, codeType]], switches)
    match Operands.carrier before, Operands.carrier after with
    | Joined first, Joined second -> Assert.Equal(f.FirstRead, first.Read); Assert.Equal(f.LatestRead, second.Read)
    | other -> failwithf "Mutable snapshots acquired a fictitious exact identity: %A" other

[<Fact>]
let ``immutable lambda binding still forwards the already witnessed function value`` () =
    let f = fixture ()
    let output = observe Alex.Witnesses.BindingWitness.nanopass (f.Root |> atChild f.ImmutableFunction) 64 (inputs f)
    Assert.Equal(inputValue f.Initial, Operands.code (callable output))
    Assert.Empty(output.InlineOps)

[<Fact>]
let ``mutable lambda binding rejects a missing initializer value`` () =
    let f = fixture ()
    let output = observe Alex.Witnesses.BindingWitness.nanopass (f.Root |> atChild f.Cell) 64 (MLIRAccumulator.empty ())
    match output.Result with
    | TRError diagnostic -> Assert.Equal("Mutable binding 'selectedThunk': Initial value not yet witnessed", diagnostic.Message)
    | other -> failwithf "Missing initializer was accepted: %A" other
    Assert.Empty(output.InlineOps)

[<Fact>]
let ``mutable function read rejects a missing binding value`` () =
    let f = fixture ()
    let output = observe Alex.Witnesses.VarRefWitness.nanopass (f.Root |> atChild f.LatestRead) 64 (inputs f)
    match output.Result with
    | TRError diagnostic -> Assert.Equal("VarRef 'selectedThunk': Binding not yet witnessed", diagnostic.Message)
    | other -> failwithf "Missing mutable cell was accepted: %A" other
    Assert.Empty(output.InlineOps)

[<Fact>]
let ``mutable read retracts after a write changes even when prior cell operands remain`` () =
    let f, operands, _, _, _, _ = stages 64
    let assignment = f.Graph.Nodes[f.Assignment]
    let changed = { assignment with Kind = SemanticKind.Set(f.Target, f.Initial); Children = [f.Target; f.Initial] }
    // The source owner publishes nothing for the changed write census, so the revision
    // holds the empty Emission.
    let graph =
        { f.Graph with Nodes = f.Graph.Nodes.Add(assignment.Id, changed)
                       Emission = Empty.emission }
        |> declareTraversalReadings
    let position = Zipper.create graph f.LatestRead |> require "Missing changed read"
    let ctx = context position 64 operands
    let snapshots = MLIRAccumulator.snapshotOperands operands
    // Exercise the actual read Pattern directly against the revision that lacks
    // the storage protocol of the cell.
    let read = Alex.Patterns.MutableCallablePatterns.pReadMutableCallable ctx f.Cell f.LatestRead
    match matchAt read position 64 operands with
    | Result.Error reason -> Assert.Contains("Mutable callable storage lacks its source-published complete protocol.", reason)
    | Result.Ok _ -> failwith "Stale source evidence admitted a mutable read"
    Assert.Same(snapshots.Callables, operands.CallableAssoc)
    Assert.Same(snapshots.CallableCells, operands.CallableCellAssoc)
    Assert.Empty(operands.AllOps)

[<Fact>]
let ``scoped operand snapshots retain the shared cell beside callable value snapshots`` () =
    let f, operands, cell, before, _, _ = stages 64
    let scope = MLIRAccumulator.snapshotOperands operands
    MLIRAccumulator.bindNode f.Cell (V(9999, 0)) TIndex operands
    Assert.Equal(None, MLIRAccumulator.recallCallableCell f.Cell operands)
    MLIRAccumulator.restoreOperands scope operands
    let restored = MLIRAccumulator.recallCallableCell f.Cell operands |> require "Lost scoped callable cell"
    Assert.Equal(Operands.cellDiscriminator cell, Operands.cellDiscriminator restored)
    let saved = MLIRAccumulator.recallCallable f.Snapshot operands |> require "Lost scoped value snapshot"
    Assert.Equal(Operands.code before, Operands.code saved)
    let output = observe Alex.Witnesses.VarRefWitness.nanopass (f.Root |> atChild f.LatestRead) 64 operands
    Assert.Equal(codeType, (Operands.code (callable output)).Type)

let private run command arguments (input: string) =
    let start = ProcessStartInfo(command, UseShellExecute = false, RedirectStandardInput = true,
                                RedirectStandardOutput = true, RedirectStandardError = true)
    for argument in arguments do start.ArgumentList.Add argument
    use child = new Process(StartInfo = start)
    if not (child.Start()) then failwithf "Cannot start %s" command
    let stdout, stderr = child.StandardOutput.ReadToEndAsync(), child.StandardError.ReadToEndAsync()
    child.StandardInput.Write input
    child.StandardInput.Close()
    if not (child.WaitForExit 20000) then
        child.Kill(true)
        child.WaitForExit()
        failwith "Mutable closure component verification timed out"
    let output, errors = stdout.GetAwaiter().GetResult(), stderr.GetAwaiter().GetResult()
    Assert.True(child.ExitCode = 0, $"{command} exited {child.ExitCode}:\n{errors}\nInput:\n{input}")
    output

let private mlirOpt arguments input = run "mlir-opt" arguments input

[<Theory>]
[<InlineData(32)>]
[<InlineData(64)>]
let ``witnessed closure cell and snapshot verify and lower through standard MLIR`` pointerBits =
    let f, _, _, snapshot, current, outputs = stages pointerBits
    let implementations =
        [f.Initial, false; f.Replacement, true] |> List.map (fun (source, value) ->
            let carrier = f.Graph.Codata.CallableCarriers[source]
            let symbol = Alex.CodeGeneration.CallableSymbols.lambda f.Graph f.Graph.Nodes[carrier.Implementation] false
            let result = { SSA = V(NodeId.value carrier.Implementation, 0); Type = boolean }
            MLIROp.FuncOp(FuncOp.FuncDef(symbol, [Arg 0, unitType], [boolean],
                [MLIROp.ArithOp(ArithOp.ConstI(result.SSA, (if value then 1L else 0L), boolean))
                 MLIROp.FuncOp(FuncOp.Return [result])], FuncVisibility.Private)))
    let inputOps =
        [f.Initial; f.Replacement] |> List.map (fun source ->
            let carrier = f.Graph.Codata.CallableCarriers[source]
            let symbol = Alex.CodeGeneration.CallableSymbols.lambda f.Graph f.Graph.Nodes[carrier.Implementation] false
            MLIROp.FuncOp(FuncOp.FuncConstant((inputValue source).SSA, symbol, codeType)))
    // Invoke both actual function operands after the write. This artifact is
    // also suitable for the native oracle: saved=false and current=true.
    let savedResult = { SSA = V(900001, 0); Type = boolean }
    let currentResult = { SSA = V(900001, 1); Type = boolean }
    let unitArgument = { SSA = V(900001, 2); Type = unitType }
    let body = inputOps @ (outputs |> List.collect _.InlineOps) @
               [MLIROp.ArithOp(ArithOp.ConstI(unitArgument.SSA, 0L, unitType))
                MLIROp.FuncOp(FuncOp.FuncCallIndirect([savedResult], (Operands.code snapshot).SSA, [unitArgument]))
                MLIROp.FuncOp(FuncOp.FuncCallIndirect([currentResult], (Operands.code current).SSA, [unitArgument]))
                MLIROp.FuncOp(FuncOp.Return [savedResult; currentResult])]
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("closure_snapshot", [], [boolean; boolean], body, FuncVisibility.Public))
    let read ordinal ty : Val = { SSA = V(900002, ordinal); Type = ty }
    let saved, latest, truth, unchanged, passed = read 0 boolean, read 1 boolean, read 2 boolean, read 3 boolean, read 4 boolean
    let zero, one, status = read 5 unitType, read 6 unitType, read 7 unitType
    let main = MLIROp.FuncOp(FuncOp.FuncDef("main", [], [unitType],
        [MLIROp.FuncOp(FuncOp.FuncCall([saved; latest], "closure_snapshot", []))
         MLIROp.ArithOp(ArithOp.ConstI(truth.SSA, 1L, boolean))
         MLIROp.ArithOp(ArithOp.XorI(unchanged.SSA, saved.SSA, truth.SSA, boolean))
         MLIROp.ArithOp(ArithOp.AndI(passed.SSA, unchanged.SSA, latest.SSA, boolean))
         MLIROp.ArithOp(ArithOp.ConstI(zero.SSA, 0L, unitType))
         MLIROp.ArithOp(ArithOp.ConstI(one.SSA, 1L, unitType))
         MLIROp.ArithOp(ArithOp.Select(status.SSA, passed.SSA, zero.SSA, one.SSA, unitType))
         MLIROp.FuncOp(FuncOp.Return [status])], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok pointerBits) "mutable_closure_component" (implementations @ [definition; main])
    let verified = mlirOpt ["--verify-each"] text
    Assert.Contains("memref<1xindex>", verified)
    Assert.Contains("scf.index_switch", verified)
    // The stock Func printer elides its dialect prefix inside func.func.
    Assert.Contains("call_indirect", verified)
    Assert.DoesNotContain("memref<2xindex>", verified)
    Assert.DoesNotContain("unrealized_conversion_cast", verified)
    let atWidth pass = $"{pass}{{index-bitwidth={pointerBits}}}"
    let passes =
        ["convert-scf-to-cf"; "expand-strided-metadata"; "memref-expand"; atWidth "finalize-memref-to-llvm"
         atWidth "convert-index-to-llvm"; atWidth "convert-func-to-llvm"; atWidth "convert-arith-to-llvm"
         "convert-cf-to-llvm"; "reconcile-unrealized-casts"]
    let lowered = mlirOpt ["--verify-each"; "--pass-pipeline=builtin.module(" + String.concat "," passes + ")"] verified
    Assert.Contains("llvm.func @closure_snapshot", lowered)
    Assert.Contains("llvm.alloca", lowered)
    Assert.Contains("llvm.store", lowered)
    Assert.Contains("llvm.load", lowered)
    Assert.DoesNotContain("memref.", lowered)
    Assert.DoesNotContain("unrealized_conversion_cast", lowered)
    if pointerBits = 64 then
        let directory = Path.Combine(Path.GetTempPath(), "composer-mutable-callable-" + System.Guid.NewGuid().ToString("N"))
        Directory.CreateDirectory directory |> ignore
        let llvm = run "mlir-translate" ["--mlir-to-llvmir"] lowered
        let input, executable = Path.Combine(directory, "snapshot.ll"), Path.Combine(directory, "snapshot")
        File.WriteAllText(input, llvm)
        run "clang" [input; "-O0"; "-o"; executable] "" |> ignore
        Assert.Equal("", run executable [] "")
        Directory.Delete(directory, true)
