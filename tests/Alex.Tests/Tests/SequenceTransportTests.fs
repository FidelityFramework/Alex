module Alex.Tests.SequenceTransportTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
open Alex.Patterns.SequencePatterns
module Operands = Alex.Traversal.SequenceOperands
module Zipper = Alex.Traversal.PSGZipper

let private ok = function Result.Ok value -> value | Result.Error reason -> failwith reason

/// Supplied component contracts, not a source lifetime/admission proof. Two
/// different generators have the same complete empty-enumerator protocol.
let private fixture () =
    // The revision states the twenty nodes, the edge set, the flow, family and frame rows
    // the fixture declares, and the two Emission tables the Patterns read: the value shape
    // of every node and the sequence contract of every flow occurrence.
    let sequenceType = sequenceOf boolType
    let iteratorType = enumeratorOf boolType
    let signature = functionFrom iteratorType boolType
    let stateField: SettledField =
        { Name = "state"; Slot = SettledSlot.Integer(8, None); Offset = Some 0; Size = Some 1; Align = Some 1 }
    // One member is six nodes in creation order: state, current, formal, body, generator, owner.
    let memberFrame name number =
        let state = node number (SemanticKind.PatternBinding (name + "State")) intType [] None
        let current = node (number + 1) (SemanticKind.PatternBinding (name + "Current")) boolType [] None
        let formal = node (number + 2) (SemanticKind.PatternBinding (name + "Frame")) iteratorType [] (Some (number + 4))
        let body = node (number + 3) (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] (Some (number + 4))
        let generator =
            node (number + 4)
                 (SemanticKind.Lambda([name + "Frame", iteratorType, formal.Id], body.Id, [], None, LambdaContext.SeqGenerator))
                 signature [number + 2; number + 3] (Some (number + 5))
        let owner = node (number + 5) (SemanticKind.SeqExpr(generator.Id, [])) sequenceType [number + 4] None
        let slot: ContinuationSlot =
            { Source = state.Id; ValueType = intType; IsCapture = false
              Holds = CaptureSlotKind.Scalar stateField.Slot; Field = stateField }
        let frame: ContinuationFrame =
            { Owner = owner.Id; Generator = generator.Id; Formal = formal.Id; State = state.Id; Current = current.Id
              Slots = [slot]; Bytes = 1; Alignment = 1; ScratchSlots = []; ScratchBytes = 0; ScratchAlignment = 1
              Initializers = []; ResumeStates = [0]; Obligations = [] }
        let contract: SequenceFamilyMember =
            { Generator = generator.Id; Formal = formal.Id; Signature = signature; State = state.Id; Current = None
              Slots = [slot]; Captures = Set.empty; Uninitialized = Set.empty; Obligations = [] }
        [state; current; formal; body; generator; owner], owner.Id, frame, contract
    let firstNodes, first, firstFrame, firstMember = memberFrame "first" 0
    let secondNodes, second, secondFrame, secondMember = memberFrame "second" 6
    let alias = node 12 (SemanticKind.Binding("alias", false, false, None)) sequenceType [5] (Some 15)
    let reference = node 13 (SemanticKind.VarRef("alias", Some alias.Id)) sequenceType [] (Some 14)
    let annotation = node 14 (SemanticKind.TypeAnnotation(reference.Id, sequenceType)) sequenceType [13] (Some 15)
    let block = node 15 (SemanticKind.Sequential [alias.Id; annotation.Id]) sequenceType [12; 14] None
    let condition = node 16 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] (Some 19)
    let left = node 17 (SemanticKind.VarRef("first", Some first)) sequenceType [] (Some 19)
    let right = node 18 (SemanticKind.VarRef("second", Some second)) sequenceType [] (Some 19)
    let choice = node 19 (SemanticKind.IfThenElse(condition.Id, left.Id, Some right.Id)) sequenceType [16; 17; 18] None
    let flows =
        [first, Set.singleton first; second, Set.singleton second
         alias.Id, Set.singleton first; reference.Id, Set.singleton first
         annotation.Id, Set.singleton first; block.Id, Set.singleton first
         left.Id, Set.singleton first; right.Id, Set.singleton second
         choice.Id, Set.ofList [first; second]]
        |> List.map (fun (id, owners) ->
            id, ({ Occurrence = id; ElementType = boolType; IsEnumerator = false
                   Owners = owners; Unknown = Set.empty }: SequenceFlow))
        |> Map.ofList
    let family: SequenceFamily =
        { Identity = first; ElementType = boolType; Participants = flows.Keys |> Set.ofSeq
          Members = Map.ofList [first, firstMember; second, secondMember]
          Bytes = 1; Alignment = 1; StateField = stateField; CurrentField = None; CurrentRepresentation = None }
    let edge sources target relation role ordinal : Hyperedge =
        { Sources = List.map NodeId sources; Target = NodeId target; Class = relation; Role = role; Ordinal = ordinal }
    // The relations the node kinds imply, in node order.
    let kindEdges =
        [edge [2] 4 EdgeClass.Structural EdgeRole.Parameter 0
         edge [3] 4 EdgeClass.Structural EdgeRole.Body 0
         edge [4] 5 EdgeClass.Structural EdgeRole.Body 0
         edge [8] 10 EdgeClass.Structural EdgeRole.Parameter 0
         edge [9] 10 EdgeClass.Structural EdgeRole.Body 0
         edge [10] 11 EdgeClass.Structural EdgeRole.Body 0
         edge [5] 12 EdgeClass.Structural EdgeRole.Attached 0
         edge [12] 13 EdgeClass.Reference EdgeRole.Definition 0
         edge [13] 14 EdgeClass.Structural EdgeRole.Operand 0
         edge [12] 15 EdgeClass.Structural EdgeRole.Element 0
         edge [14] 15 EdgeClass.Structural EdgeRole.Element 1
         edge [5] 17 EdgeClass.Reference EdgeRole.Definition 0
         edge [11] 18 EdgeClass.Reference EdgeRole.Definition 0
         edge [16] 19 EdgeClass.Structural EdgeRole.Guard 0
         edge [17] 19 EdgeClass.Structural EdgeRole.ThenBranch 0
         edge [18] 19 EdgeClass.Structural EdgeRole.ElseBranch 0]
    let layoutEdges: Hyperedge list =
        family.Members |> Map.toList |> List.map (fun (owner, memberContract) ->
            { Sources = List.distinct (List.ofSeq family.Members.Keys @
                            [memberContract.Generator; memberContract.Formal; memberContract.State] @
                            (memberContract.Slots |> List.map _.Source) @ memberContract.Obligations)
              Target = owner; Class = EdgeClass.Suspension; Role = EdgeRole.SequenceFamilyLayout; Ordinal = 0 })
    let data number = NodeId number, CallableValueShape.Data (NodeId number)
    let callable number = NodeId number, CallableValueShape.Callable (NodeId number)
    let sequence number = NodeId number, CallableValueShape.Sequence (NodeId number)
    // A generator formal is the frame storage itself. Its shape is data.
    let shapes =
        Map.ofList
            [data 0; data 1; data 2; data 3; callable 4; sequence 5
             data 6; data 7; data 8; data 9; callable 10; sequence 11
             sequence 12; sequence 13; sequence 14; sequence 15
             data 16; sequence 17; sequence 18; sequence 19]
    let contracts = flows |> Map.map (fun _ flow -> ({ Flow = flow; Family = family }: SequenceWitnessContract))
    let stated =
        revision (firstNodes @ secondNodes @ [alias; reference; annotation; block; condition; left; right; choice])
    let graph =
        { stated with
            Edges = kindEdges @ layoutEdges
            Codata =
                { stated.Codata with
                    SequenceFlows = flows; SequenceFamilies = Map.ofList [first, family]
                    ContinuationFrames = Map.ofList [first, firstFrame; second, secondFrame] }
            Emission =
                { stated.Emission with
                    Callable = { stated.Emission.Callable with ValueShapes = shapes }
                    Storage = { stated.Emission.Storage with Sequences = contracts } } }
    graph, first, second, alias.Id, reference.Id, annotation.Id, block.Id, condition.Id, left.Id, right.Id, choice.Id

let private context graph position accumulator =
    let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
    let visited = ref Set.empty
    { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
      ScopeContext = scope; RootScopeContext = scope; Graph = graph; Zipper = position
      GlobalVisited = visited; TraversalVisited = visited }

let private seed ctx occurrence codeIndex environmentIndex =
    let shape = Operands.project ctx occurrence |> ok
    let code = { SSA = Arg codeIndex; Type = Operands.functionType shape }
    let environment = { SSA = Arg environmentIndex; Type = Operands.environmentType shape }
    Operands.bind ctx occurrence code environment |> ok
    [code; environment]

[<Fact>]
let ``passive sequence binding read annotation and block retain the actual pair`` () =
    let graph, first, _, alias, reference, annotation, block, _, _, _, _ = fixture ()
    let operands = MLIRAccumulator.empty ()
    let root = Zipper.create graph block |> require "Missing block"
    let original = seed (context graph root operands) first 0 1
    let witnesses =
        [alias, atChild alias root, Alex.Witnesses.BindingWitness.nanopass
         reference, atChild annotation root |> atChild reference, Alex.Witnesses.VarRefWitness.nanopass
         annotation, atChild annotation root, Alex.Witnesses.TypeAnnotationWitness.nanopass
         block, root, Alex.Witnesses.StructuralWitness.nanopass]
    for id, position, witness in witnesses do
        let ctx = context graph position operands
        let output = witness.Witness ctx graph.Nodes[id]
        match output.Result with
        | TRSequence value ->
            Assert.Equal<Val list>(original, Operands.values value)
            MLIRAccumulator.bindSequence id value operands |> ok
        | other -> failwithf "Lost sequence pair: %A" other
        Assert.Empty output.InlineOps
        Assert.Empty output.TopLevelOps
        Assert.True((MLIRAccumulator.recallNode id operands).IsNone)
        Assert.Same(position, ctx.Zipper)
        Assert.Empty ctx.TraversalVisited.Value

[<Fact>]
let ``sequence forward rejects scalar fallback missing flow and wrong occurrence`` () =
    let graph, first, _, alias, reference, annotation, block, _, _, _, _ = fixture ()
    let operands = MLIRAccumulator.empty ()
    let root = Zipper.create graph block |> require "Missing block"
    let position = atChild alias root
    let ctx = context graph position operands
    MLIRAccumulator.bindNode first (Arg 0) (TMemRefStatic(1, TInt(IntWidth 8))) operands
    match matchAt (pSequenceForward ctx first) position 64 operands with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "A raw environment silently substituted for a sequence pair"
    seed ctx first 1 2 |> ignore
    let different = atChild annotation root |> atChild reference
    match matchAt (pSequenceForward ctx first) different 64 operands with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "A foreign Huet occurrence was accepted"
    // The flow row of the alias is removed. The first revision is the fixture without
    // that row and without the contract published from it. The second revision holds
    // the empty Emission, as a graph for which the source owner publishes nothing.
    let lacking =
        { graph with
            Codata = { graph.Codata with SequenceFlows = graph.Codata.SequenceFlows.Remove alias }
            Emission =
                { graph.Emission with
                    Storage = { graph.Emission.Storage with Sequences = graph.Emission.Storage.Sequences.Remove alias } } }
    for changed in [lacking; { lacking with Emission = Empty.emission }] do
        let position = Zipper.create changed block |> require "Missing block" |> atChild alias
        let ctx = context changed position operands
        match matchAt (pSequenceForward ctx first) position 64 operands with
        | Result.Error _ -> ()
        | Result.Ok _ -> failwith "Missing destination flow was reconstructed"

[<Fact>]
let ``conditional returns both components of the same selected alternative`` () =
    let graph, _, _, _, _, _, _, _, left, right, choice = fixture ()
    let operands = MLIRAccumulator.empty ()
    let position = Zipper.create graph choice |> require "Missing conditional"
    let ctx = context graph position operands
    let leftValues = seed ctx left 0 1
    let rightValues = seed ctx right 2 3
    let condition = { SSA = Arg 4; Type = TInt(IntWidth 1) }
    match matchAt (pSequenceConditional ctx condition left [] right []) position 64 operands with
    | Result.Ok (([MLIROp.IndexOp(IndexOp.IndexCastU(selector, test, _, TIndex));
                    MLIROp.SCFOp(SCFOp.IndexSwitch(actual, cases, fallback, results))], TRSequence value), _) ->
        Assert.Equal(condition.SSA, test)
        Assert.Equal(selector, actual)
        let label, branch = Assert.Single cases
        Assert.Equal(1L, label)
        let yielded = function
            | [MLIROp.SCFOp(SCFOp.Yield values)] -> values
            | operations -> failwithf "Wrong branch operations: %A" operations
        Assert.Equal<(SSA * MLIRType) list>(leftValues |> List.map (fun value -> value.SSA, value.Type), yielded branch)
        Assert.Equal<(SSA * MLIRType) list>(rightValues |> List.map (fun value -> value.SSA, value.Type), yielded fallback)
        Assert.Equal<(SSA * MLIRType) list>(Operands.values value |> List.map (fun value -> value.SSA, value.Type), results)
    | other -> failwithf "Conditional did not transport a selected pair: %A" other

[<Fact>]
let ``join cannot discard a possible source owner`` () =
    let graph, _, _, _, _, _, _, _, left, right, choice = fixture ()
    let narrowed = { graph.Codata.SequenceFlows[left] with Occurrence = choice }
    // The source owner publishes the narrowed flow of the conditional in its contract.
    let changed =
        { graph with
            Codata = { graph.Codata with SequenceFlows = graph.Codata.SequenceFlows.Add(choice, narrowed) }
            Emission =
                { graph.Emission with
                    Storage =
                        { graph.Emission.Storage with
                            Sequences =
                                graph.Emission.Storage.Sequences.Add(
                                    choice, { graph.Emission.Storage.Sequences[choice] with Flow = narrowed }) } } }
    let operands = MLIRAccumulator.empty ()
    let position = Zipper.create changed choice |> require "Missing conditional"
    let ctx = context changed position operands
    seed ctx left 0 1 |> ignore
    seed ctx right 2 3 |> ignore
    match matchAt (pSequenceConditional ctx { SSA = Arg 4; Type = TInt(IntWidth 1) } left [] right []) position 64 operands with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "Join selected one possible origin and silently discarded another"

[<Fact>]
let ``a generator raw frame formal cannot acquire a sequence pair from a flow row`` () =
    let graph, first, _, _, _, _, _, _, _, _, _ = fixture ()
    let codata = graph.Codata
    let formal = codata.ContinuationFrames[first].Formal
    let family = codata.SequenceFamilies[first]
    let forgedFlow = { codata.SequenceFlows[first] with Occurrence = formal; IsEnumerator = true }
    let widened = { family with Participants = family.Participants.Add formal }
    // The source owner publishes the widened family in every contract. It publishes no
    // contract for the formal, whose shape is data.
    let changed =
        { graph with
            Codata = { codata with
                        SequenceFlows = codata.SequenceFlows.Add(formal, forgedFlow)
                        SequenceFamilies = codata.SequenceFamilies.Add(first, widened) }
            Emission =
                { graph.Emission with
                    Storage =
                        { graph.Emission.Storage with
                            Sequences =
                                graph.Emission.Storage.Sequences
                                |> Map.map (fun _ contract -> { contract with Family = widened }) } } }
    let position = Zipper.create changed formal |> require "Missing generator formal"
    match Operands.project (context changed position (MLIRAccumulator.empty ())) formal with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "An actual storage formal was expanded into a source sequence protocol"

[<Theory>]
[<InlineData("extent")>]
[<InlineData("holds")>]
[<InlineData("value-type")>]
[<InlineData("authority")>]
let ``sequence projection rejects changed actual frame under an unchanged family`` defect =
    let graph, first, second, _, _, _, _, _, _, _, choice = fixture ()
    let frame = graph.Codata.ContinuationFrames[second]
    let changedFrame =
        match defect with
        | "holds" -> { frame with Slots = frame.Slots |> List.map (fun slot -> { slot with Holds = CaptureSlotKind.CellView intType }) }
        | "value-type" -> { frame with Slots = frame.Slots |> List.map (fun slot -> { slot with ValueType = boolType }) }
        | _ ->
            { frame with Bytes = 2
                         Slots = frame.Slots |> List.map (fun slot -> { slot with Field = { slot.Field with Offset = Some 1 } }) }
    let changed =
        { graph with Codata = { graph.Codata with
                                  ContinuationFrames = graph.Codata.ContinuationFrames.Add(second, changedFrame) } }
    let changed =
        if defect = "authority" then
            { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.SequenceFamilyLayout || edge.Target <> second) }
        else changed
    // The source owner publishes nothing for the changed graph, so the revision holds
    // the empty Emission.
    let changed = { changed with Emission = Empty.emission }
    let position = Zipper.create changed choice |> require "Missing conditional"
    let ctx = context changed position (MLIRAccumulator.empty ())
    // The first alternative itself is unchanged; the entire advertised family
    // must still agree with every actual member before any pair is admitted.
    match Operands.project ctx first with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "A stale family concealed a changed alternative's frame layout"

[<Fact>]
let ``sequence projection rejects changed actual generator formal and signature`` () =
    let graph, first, second, _, _, _, _, _, _, _, choice = fixture ()
    let frame = graph.Codata.ContinuationFrames[second]
    let formal = graph.Nodes[frame.Formal]
    let generator = graph.Nodes[frame.Generator]
    let wrongFormalType = enumeratorOf intType
    let changedGenerator =
        match generator.Kind with
        | SemanticKind.Lambda([name, _, parameter], body, captures, recursive, context) ->
            { generator with Type = functionFrom wrongFormalType boolType
                             Kind = SemanticKind.Lambda([name, wrongFormalType, parameter], body, captures, recursive, context) }
        | _ -> failwith "Fixture lost its generator"
    // The source owner publishes nothing for the changed graph, so the revision holds
    // the empty Emission.
    let changed =
        { graph with Nodes = graph.Nodes.Add(formal.Id, { formal with Type = wrongFormalType }).Add(generator.Id, changedGenerator)
                     Emission = Empty.emission }
    let position = Zipper.create changed choice |> require "Missing conditional"
    let ctx = context changed position (MLIRAccumulator.empty ())
    match Operands.project ctx first with
    | Result.Error _ -> ()
    | Result.Ok _ -> failwith "A stale family concealed a changed alternative's generator signature"

[<Fact>]
let ``operation scope restore keeps sequence pairs and their physical types together`` () =
    let graph, first, _, alias, _, _, block, _, _, _, _ = fixture ()
    let position = Zipper.create graph block |> require "Missing block"
    let operands = MLIRAccumulator.empty ()
    let ctx = context graph position operands
    let original = seed ctx first 0 1
    let outer = MLIRAccumulator.snapshotOperands operands
    let shape = Operands.project ctx first |> ok
    let code = { SSA = V(900, 0); Type = Operands.functionType shape }
    let environment = { SSA = V(900, 1); Type = Operands.environmentType shape }
    Operands.bind ctx first code environment |> ok
    Operands.copy ctx first alias |> ok
    MLIRAccumulator.restoreOperands outer operands
    Assert.Same(outer.Sequences, operands.SequenceAssoc)
    Assert.Same(outer.Scalars, operands.NodeAssoc)
    Assert.Same(outer.Types, operands.SSATypes)
    Assert.True((MLIRAccumulator.recallSequence alias operands).IsNone)
    Assert.True((MLIRAccumulator.recallSSAType code.SSA operands).IsNone)
    Assert.True((MLIRAccumulator.recallSSAType environment.SSA operands).IsNone)
    let restored = MLIRAccumulator.recallSequence first operands |> require "Sequence pair was lost"
    Assert.Equal<Val list>(original, Operands.values restored)
