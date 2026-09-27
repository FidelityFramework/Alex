module Alex.Tests.ContinuationPatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Patterns.ContinuationPatterns
open Alex.Patterns.ControlFlowPatterns
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

let private scalar slot = ValueRepresentation.Scalar slot
let private buffer element = ValueRepresentation.Buffer(None, element)

/// The revision with the occurrence representations given stated in its numeric table.
let private representing (forms: (NodeId * ValueRepresentation) list) (held: Revision) : Revision =
    let stated =
        forms |> List.fold (fun table (id, form) -> Map.add id (Ok form) table) held.Emission.Numeric.OccurrenceRepresentations
    { held with Emission = { held.Emission with Numeric = { held.Emission.Numeric with OccurrenceRepresentations = stated } } }

// The fixtures hold no platform description and no proof of an index transport. The
// fields of a transport that name them hold an identity that no node of a revision
// carries. No Pattern under test reads those fields.
let private notStated = NodeId -1

/// The carrier of a scalar occurrence: the slot and the range given, and no
/// representation declaration.
let private carrier (site: SemanticNode) slot range : ScalarCarrier =
    { Site = site.Id; Slot = slot; Range = range; Representation = None; Declaration = None
      SourceType = site.Type; Obligations = []; Participants = Set.singleton site.Id }

/// The transport of a dispatch selector into an index domain of 64 bits.
let private transport (site: NodeId) (selector: ScalarCarrier) unsigned : NumericIndexTransport =
    { Site = site; Operand = selector.Site; Carrier = selector
      PointerDeclaration = notStated; PointerBits = 64; Unsigned = unsigned
      Capacity =
        if unsigned then ValueRange.Bounded(0I, 18446744073709551615I)
        else ValueRange.Bounded(-9223372036854775808I, 9223372036854775807I)
      Obligation = notStated
      Participants = Set.ofList [selector.Site; site] }

let private transporting (row: NumericIndexTransport) (held: Revision) : Revision =
    { held with
        Emission = { held.Emission with
                        Numeric = { held.Emission.Numeric with
                                        IndexTransports = held.Emission.Numeric.IndexTransports.Add(row.Site, row) } } }

// Component inputs are already settled and initialized by the caller. These
// tests establish witness composition, not Baker liveness or source conformance.
let private fixture descriptor =
    let source = node 0 (SemanticKind.PatternBinding "captured") boolType [] None
    let frame = node 1 (SemanticKind.PatternBinding "frame") (arrayOf boolType) [] None
    let value = node 2 (SemanticKind.PatternBinding "replacement") boolType [] None
    let read = node 3 (SemanticKind.FrameRead(frame.Id, source.Id)) boolType [1] None
    let write = node 4 (SemanticKind.FrameWrite(frame.Id, source.Id, value.Id)) unitType [1; 2] None
    let root = node 5 (SemanticKind.Sequential [write.Id; read.Id]) boolType [4; 3] None
    // The occurrence representations are those the compiler service publishes for these nodes.
    let graph =
        revision [source; frame; value; read; write; root]
        |> representing [ source.Id, scalar SettledSlot.Bool
                          frame.Id, buffer (scalar SettledSlot.Bool)
                          value.Id, scalar SettledSlot.Bool
                          read.Id, scalar SettledSlot.Bool
                          write.Id, scalar SettledSlot.Unit
                          root.Id, scalar SettledSlot.Bool ]
    let position = Zipper.create graph root.Id |> require "Missing frame fixture root"
    let slot: ContinuationSlot =
        { Source = source.Id; ValueType = boolType; IsCapture = true
          Holds = if descriptor then CaptureSlotKind.CellView boolType else CaptureSlotKind.Scalar SettledSlot.Bool
          Field = { Name = "captured"; Slot = if descriptor then SettledSlot.Pointer 5 else SettledSlot.Bool
                    Offset = Some 8; Size = Some(if descriptor then 40 else 1); Align = Some(if descriptor then 8 else 1) } }
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode frame.Id (Arg 0) (TMemRefStatic(64, TInt(IntWidth 8))) operands
    MLIRAccumulator.bindNode value.Id (Arg 1) (TInt(IntWidth 1)) operands
    position, frame.Id, value.Id, read.Id, write.Id, slot, operands

let private observe pattern (position: Zipper.PSGZipper) operands =
    let graph, nodes, edges, codata = position.Graph, position.Graph.Nodes, position.Graph.Edges, position.Graph.Codata
    let result = matchAt pattern position 64 operands
    Assert.Same(graph, position.Graph)
    Assert.Same(nodes, position.Graph.Nodes)
    Assert.Same(edges, position.Graph.Edges)
    Assert.Same(codata, position.Graph.Codata)
    match result with
    | Result.Ok (_, next) ->
        Assert.Equal(position.Focus.Id, next.Focus.Id)
        Assert.Same(position.Path, next.Path)
    | _ -> ()
    result

let private composed descriptor =
    let position, frame, value, read, write, slot, operands = fixture descriptor
    let written =
        match observe (pWriteContinuationSlot write frame value 64 slot) (position |> atChild write) operands with
        | Result.Ok ((ops, TRVoid), _) -> ops
        | other -> failwithf "Frame write failed: %A" other
    match observe (pReadContinuationSlot read frame 64 slot) (position |> atChild read) operands with
    | Result.Ok ((ops, TRValue result), _) -> written @ ops, result
    | other -> failwithf "Frame read failed: %A" other

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``scalar and captured-cell frame access verify and lower with typed descriptors`` descriptor =
    let operations, value = composed descriptor
    Assert.Equal(TInt(IntWidth 1), value.Type)
    let functionOp = MLIROp.FuncOp(FuncOp.FuncDef("frame_component",
        [Arg 0, TMemRefStatic(64, TInt(IntWidth 8)); Arg 1, TInt(IntWidth 1)], [value.Type],
        operations @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = value.SSA; Type = value.Type }]))], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "frame_component" [functionOp]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    if descriptor then
        Assert.Contains("memref<1xmemref<1xi1>>", verified)
        // Writes load the original descriptor then store into that cell; they
        // neither allocate a replacement nor overwrite the descriptor slot.
        Assert.DoesNotContain("memref.alloc", verified)
        Assert.DoesNotContain("memref.store %arg1, %arg0", verified)
    let pipeline = "builtin.module(expand-strided-metadata,memref-expand,finalize-memref-to-llvm{index-bitwidth=64},convert-index-to-llvm{index-bitwidth=64},convert-func-to-llvm{index-bitwidth=64},convert-arith-to-llvm{index-bitwidth=64},reconcile-unrealized-casts)"
    let lowered = Alex.Tests.Tools.mlirOpt ["--verify-each"; "--pass-pipeline=" + pipeline] verified
    Assert.Contains("llvm.func @frame_component", lowered)
    Assert.Contains("llvm.store", lowered)
    Assert.DoesNotContain("unrealized_conversion_cast", lowered)

[<Theory>]
[<InlineData("placement", "has no complete placement")>]
[<InlineData("descriptor", "requires a complete descriptor field")>]
[<InlineData("carrier", "does not have its settled 64-byte carrier")>]
[<InlineData("operand", "write lacks its settled operand representation")>]
[<InlineData("missing", "not yet witnessed")>]
let ``frame access rejects absent or inconsistent settled prerequisites`` defect reason =
    let position, frame, value, _, write, original, operands = fixture true
    let slot =
        match defect with
        | "placement" -> { original with Field = { original.Field with Offset = None } }
        | "descriptor" -> { original with Field = { original.Field with Slot = SettledSlot.Pointer 1 } }
        | _ -> original
    if defect = "carrier" then MLIRAccumulator.bindNode frame (Arg 0) (TMemRef(TInt(IntWidth 8))) operands
    if defect = "operand" then MLIRAccumulator.bindNode value (Arg 1) (TInt(IntWidth 32)) operands
    if defect = "missing" then operands.NodeAssoc <- operands.NodeAssoc.Remove frame
    match observe (pWriteContinuationSlot write frame value 64 slot) (position |> atChild write) operands with
    | Result.Error message -> Assert.Contains(reason, message)
    | Result.Ok _ -> failwithf "Frame prerequisite '%s' was silently accepted" defect

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``frame borrow preserves the existing scalar cell without copying its payload`` descriptor =
    let original, frame, _, read, _, slot, operands = fixture descriptor
    // The compiler service publishes the same rows for the borrow as for the read it replaces.
    let graph = { original.Graph with Nodes = original.Graph.Nodes.Add(read, { original.Graph.Nodes[read] with Kind = SemanticKind.FrameBorrow(frame, slot.Source) }) }
    let position = Zipper.create graph original.Focus.Id |> require "Missing borrow fixture root" |> atChild read
    match observe (pBorrowContinuationSlot read frame 64 slot) position operands with
    | Result.Ok ((operations, TRValue value), _) ->
        Assert.Equal(TMemRefStatic(1, TInt(IntWidth 1)), value.Type)
        let loads = operations |> List.filter (function MLIROp.MemRefOp(MemRefOp.LoadAligned _) -> true | _ -> false)
        Assert.Equal((if descriptor then 1 else 0), loads.Length)
        Assert.DoesNotContain(operations, function MLIROp.MemRefOp(MemRefOp.Load _ | MemRefOp.Alloca _) -> true | _ -> false)
        let definition = MLIROp.FuncOp(FuncOp.FuncDef("borrow_component", [Arg 0, TMemRefStatic(64, TInt(IntWidth 8))], [value.Type],
            operations @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = value.SSA; Type = value.Type }]))], FuncVisibility.Public))
        let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "borrow_component" [definition]
        let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
        Assert.Contains("memref.view", verified)
        Assert.DoesNotContain("unrealized_conversion_cast", verified)
    | other -> failwithf "Settled cell borrow failed: %A" other

[<Fact>]
let ``buffer-valued frame slot retains its descriptor through a static-to-dynamic view cast`` () =
    let original, frame, value, read, write, originalSlot, operands = fixture true
    let native = arrayOf boolType
    let retyped = [originalSlot.Source; value; read]
    let nodes = retyped |> List.fold (fun nodes id -> Map.add id { original.Graph.Nodes[id] with Type = native } nodes) original.Graph.Nodes
    // The compiler service publishes a buffer of bool for each occurrence of the array type.
    let graph =
        { original.Graph with Nodes = nodes }
        |> representing (retyped |> List.map (fun id -> id, buffer (scalar SettledSlot.Bool)))
    let root = Zipper.create graph original.Focus.Id |> require "Missing buffer fixture root"
    let slot = { originalSlot with ValueType = native; Holds = CaptureSlotKind.ValueView native }
    // The carrier itself is a value view, not a cell containing one.
    let actual = TMemRefStatic(3, TInt(IntWidth 1))
    operands.NodeAssoc <- operands.NodeAssoc.Add(value, (Arg 1, actual))
    operands.SSATypes <- operands.SSATypes.Add(Arg 1, actual)
    let writing =
        match observe (pWriteContinuationSlot write frame value 64 slot) (root |> atChild write) operands with
        | Result.Ok ((operations, TRVoid), _) -> operations
        | other -> failwithf "Buffer descriptor write failed: %A" other
    let reading, result =
        match observe (pReadContinuationSlot read frame 64 slot) (root |> atChild read) operands with
        | Result.Ok ((operations, TRValue result), _) -> operations, result
        | other -> failwithf "Buffer descriptor read failed: %A" other
    Assert.Equal(TMemRef(TInt(IntWidth 1)), result.Type)
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("buffer_component", [Arg 0, TMemRefStatic(64, TInt(IntWidth 8)); Arg 1, actual], [result.Type],
        writing @ reading @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = result.SSA; Type = result.Type }]))], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "buffer_component" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.Contains("memref.cast", verified)
    Assert.Contains("memref<1xmemref<?xi1>>", verified)
    Assert.DoesNotContain("unrealized_conversion_cast", verified)
    match observe (pBorrowContinuationSlot read frame 64 slot) (root |> atChild read) operands with
    | Result.Error message -> Assert.Contains("has no admitted mutable-cell borrow representation", message)
    | Result.Ok _ -> failwith "Buffer value was silently treated as a mutable cell"

[<Theory>]
[<InlineData(true)>]
[<InlineData(false)>]
let ``continuation dispatch uses the selector range without changing the graph`` unsigned =
    let selector = node 0 (SemanticKind.PatternBinding "pc") intType [] None
    let left = node 1 (SemanticKind.PatternBinding "left") boolType [] None
    let right = node 2 (SemanticKind.PatternBinding "right") boolType [] None
    let dispatch = node 3 (SemanticKind.ContinuationDispatch(selector.Id, [3, left.Id], right.Id)) boolType [0; 2; 1] (Some 4)
    let binding = node 4 (SemanticKind.Binding("result", false, false, None)) boolType [3] None
    let raw = revision [selector; left; right; dispatch; binding]
    let range = if unsigned then ValueRange.Bounded(0I, 255I) else ValueRange.Bounded(-128I, 127I)
    // The compiler service refuses this fixture: it holds no platform description. The
    // transport states the range of the selector, the carrier of eight bits that the
    // operand is recalled with, and the sign that the range has.
    let graph =
        { raw with Nodes = raw.Nodes.Add(selector.Id, { selector with ValueRange = Some range }) }
        |> transporting (transport dispatch.Id (carrier selector (SettledSlot.Integer(8, None)) range) unsigned)
    let position = Zipper.create graph binding.Id |> require "Missing dispatch fixture" |> atChild dispatch.Id
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode selector.Id (Arg 0) (TInt(IntWidth 8)) operands
    MLIRAccumulator.bindNode left.Id (Arg 1) (TInt(IntWidth 1)) operands
    MLIRAccumulator.bindNode right.Id (Arg 2) (TInt(IntWidth 1)) operands
    let result = Alex.Traversal.Values.value dispatch.Id 0
    let pattern = pBuildContinuationDispatch dispatch.Id selector.Id [3, left.Id, []] (right.Id, []) (Some(result, TInt(IntWidth 1)))
    match observe pattern position operands with
    | Result.Ok ((operations, TRValue value), _) ->
        let definition = MLIROp.FuncOp(FuncOp.FuncDef("dispatch_component",
            [Arg 0, TInt(IntWidth 8); Arg 1, TInt(IntWidth 1); Arg 2, TInt(IntWidth 1)], [value.Type],
            operations @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = value.SSA; Type = value.Type }]))], FuncVisibility.Public))
        let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "dispatch_component" [definition]
        let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
        Assert.Contains((if unsigned then "index.castu" else "index.casts"), verified)
        Assert.Contains("scf.index_switch", verified)
    | other -> failwithf "Settled dispatch failed: %A" other

// The compiler service refuses this fixture: the state holds an integer type and the
// fixture holds no platform description. The revision states the nodes and the codata
// the fixture declares, and the one emission row the Patterns under test read: the
// occurrence representation of the captured cell, the published form of bool.
let private constructionFixture () =
    let sequenceType = sequenceOf boolType
    let source = node 0 (SemanticKind.Binding("captured", true, false, None)) boolType [] None
    let state = node 1 (SemanticKind.PatternBinding "state") nintType [] None
    let current = node 2 (SemanticKind.PatternBinding "current") boolType [] None
    let formalType = pointerTo sequenceType
    let formal = node 3 (SemanticKind.PatternBinding "frame") formalType [] None
    let body = node 4 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let generator =
        node 5 (SemanticKind.Lambda(["frame", formalType, formal.Id], body.Id, [], None, LambdaContext.SeqGenerator))
               (functionFrom formalType boolType) [3; 4] None
    let template = node 6 (SemanticKind.SeqExpr(generator.Id, [])) sequenceType [5] None
    let first = node 7 (SemanticKind.PatternBinding "first") (enumeratorOf boolType) [] None
    let second = node 8 (SemanticKind.PatternBinding "second") (enumeratorOf boolType) [] None
    let read = node 9 (SemanticKind.FrameRead(second.Id, source.Id)) boolType [8] None
    let root = node 10 (SemanticKind.Sequential [template.Id; first.Id; second.Id; read.Id]) boolType [6; 7; 8; 9] None
    let proof =
        node 11 (SemanticKind.Obligation
                    { Id = "frame_component_layout"; Kind = "continuation-layout"; Logic = "QF_LIA"
                      Statement = "Supplied component frame slots occupy their declared extent"
                      Source = "Alex component fixture"; Refs = []
                      Body = ObligationBody.ContinuationLayout([0, 8, 8; 8, 1, 1; 16, 40, 8], 56, 8) }) unitType [] None
    let slot source native holds field offset size align capture : ContinuationSlot =
        { Source = source; ValueType = native; Holds = holds; IsCapture = capture
          Field = { Name = string(NodeId.value source); Slot = field; Offset = Some offset; Size = Some size; Align = Some align } }
    let slots =
        [slot state.Id nintType (CaptureSlotKind.Scalar(SettledSlot.Pointer 1)) (SettledSlot.Pointer 1) 0 8 8 false
         slot current.Id boolType (CaptureSlotKind.Scalar SettledSlot.Bool) SettledSlot.Bool 8 1 1 false
         slot source.Id boolType (CaptureSlotKind.CellView boolType) (SettledSlot.Pointer 5) 16 40 8 true]
    let plan: ContinuationFrame =
        { Owner = template.Id; Generator = generator.Id; Formal = formal.Id; State = state.Id; Current = current.Id
          Slots = slots; Bytes = 56; Alignment = 8; ScratchSlots = []; ScratchBytes = 0; ScratchAlignment = 1
          Initializers = [source.Id, source.Id]; ResumeStates = [0; 1]; Obligations = [proof.Id] }
    let raw = revision [source; state; current; formal; body; generator; template; first; second; read; root; proof]
    let graph = { raw with Codata = { Codata.empty with
                                        Escapes = [template.Id, EscapeKind.StackScoped; first.Id, EscapeKind.StackScoped; second.Id, EscapeKind.StackScoped] |> Map.ofList
                                        ContinuationFrames = Map.ofList [template.Id, plan] } }
                |> representing [source.Id, scalar SettledSlot.Bool]
    let position = Zipper.create graph root.Id |> require "Missing constructor fixture"
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.registerSSAType (Arg 0) (TMemRefStatic(1, TInt(IntWidth 1))) operands
    MLIRAccumulator.bindNode source.Id (Arg 0) (TMemRef(TInt(IntWidth 1))) operands
    position, plan, first.Id, second.Id, read.Id, operands

[<Fact>]
let ``fresh enumerators allocate distinct state and copy complete capture descriptors only`` () =
    let position, plan, first, second, read, operands = constructionFixture ()
    let emit id pattern =
        match observe pattern (position |> atChild id) operands with
        | Result.Ok ((ops, TRValue value), _) ->
            MLIRAccumulator.bindNode id value.SSA value.Type operands
            ops, value
        | other -> failwithf "Sequence component allocation failed: %A" other
    let construction, template = emit plan.Owner (pConstructSequence plan.Owner plan plan.Initializers)
    let firstOps, one = emit first (pGetEnumerator first plan.Owner plan)
    let secondOps, two = emit second (pGetEnumerator second plan.Owner plan)
    let capture = plan.Slots |> List.find _.IsCapture
    let readOps, result = emit read (pReadContinuationSlot read second plan.Bytes capture)
    Assert.NotEqual(template.SSA, one.SSA)
    Assert.NotEqual(one.SSA, two.SSA)
    let operations = construction @ firstOps @ secondOps @ readOps
    let allocations = operations |> List.choose (function MLIROp.MemRefOp(MemRefOp.Alloca(ssa, _, _)) -> Some ssa | _ -> None)
    Assert.Equal<SSA list>([template.SSA; one.SSA; two.SSA], allocations)
    let offsets = operations |> List.choose (function MLIROp.ArithOp(ArithOp.ConstI(_, offset, TIndex)) -> Some offset | _ -> None)
    Assert.DoesNotContain(8L, offsets) // The current field is neither read nor copied.
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("enumerator_component", [Arg 0, TMemRefStatic(1, TInt(IntWidth 1))], [result.Type],
        operations @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = result.SSA; Type = result.Type }]))], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "enumerator_component" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.Contains("memref<1xmemref<1xi1>>", verified)
    Assert.DoesNotContain("unrealized_conversion_cast", verified)
    let pipeline = "builtin.module(expand-strided-metadata,memref-expand,finalize-memref-to-llvm{index-bitwidth=64},convert-index-to-llvm{index-bitwidth=64},convert-func-to-llvm{index-bitwidth=64},convert-arith-to-llvm{index-bitwidth=64},reconcile-unrealized-casts)"
    let lowered = Alex.Tests.Tools.mlirOpt ["--verify-each"; "--pass-pipeline=" + pipeline] verified
    Assert.Contains("llvm.func @enumerator_component", lowered)

[<Theory>]
[<InlineData(false, "has no resident allocation obligations")>]
[<InlineData(true, "has no settled residence")>]
let ``sequence allocation requires graph allocation prerequisites`` missingResidence reason =
    let position, plan, _, _, _, operands = constructionFixture ()
    let plan = if missingResidence then plan else { plan with Obligations = [] }
    let position =
        if missingResidence then
            let graph = { position.Graph with Codata = { position.Graph.Codata with Escapes = Map.empty } }
            Zipper.create graph position.Focus.Id |> require "Missing allocation negative root"
        else position
    match observe (pConstructSequence plan.Owner plan plan.Initializers) (position |> atChild plan.Owner) operands with
    | Result.Error message -> Assert.Contains(reason, message)
    | Result.Ok _ -> failwith "Sequence allocation accepted absent graph prerequisites"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``constructor rejects an incomplete or repeated capture initializer set`` repeated =
    let position, plan, _, _, _, operands = constructionFixture ()
    let initializers = if repeated then plan.Initializers @ plan.Initializers else []
    match observe (pConstructSequence plan.Owner plan initializers) (position |> atChild plan.Owner) operands with
    | Result.Error message ->
        Assert.Contains($"Sequence constructor {NodeId.value plan.Owner} does not initialize its exact settled capture set", message)
    | Result.Ok _ -> failwith "Constructor accepted an incomplete or repeated capture set"

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``dispatch witness pulls declared child positions or identifies a missing child`` missingChild =
    let nativeIndex = NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Pointer)
    let selector = node 0 (SemanticKind.Literal(NativeLiteral.Int(0L, nativeIndex))) nintType [] None
    let left = node 1 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let right = node 2 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let dispatch = node 3 (SemanticKind.ContinuationDispatch(selector.Id, [0, left.Id], right.Id)) boolType [0; 2; 1] (Some 4)
    let binding = node 4 (SemanticKind.Binding("result", false, false, None)) boolType [3] None
    let raw = revision [selector; left; right; dispatch; binding]
    let held = if missingChild then { raw with Nodes = raw.Nodes.Remove right.Id } else raw
    // The compiler service refuses this fixture: it holds no platform description. The
    // rows below are the rows the traversal and the witnesses read for the nodes the
    // revision holds. Each literal is a result site with its carrier. The selector is a
    // native integer under a pointer width of 64 bits, and its literal is zero.
    let word = SettledSlot.Integer(64, None)
    let truth = SettledSlot.Bool, ValueRange.Bounded(0I, 1I)
    let index = carrier selector word (ValueRange.Bounded(0I, 0I))
    let literals =
        [index; carrier left (fst truth) (snd truth); carrier right (fst truth) (snd truth)]
        |> List.filter (fun literal -> held.Nodes.ContainsKey literal.Site)
    let stated =
        held
        |> representing ((dispatch.Id, scalar SettledSlot.Bool) :: (literals |> List.map (fun literal -> literal.Site, scalar literal.Slot)))
        |> transporting (transport dispatch.Id index true)
    let graph =
        { stated with
            Emission = { stated.Emission with
                            Callable = { stated.Emission.Callable with
                                            AliasTargets = literals |> List.map (fun literal -> literal.Site, literal.Site) |> Map.ofList }
                            Numeric = { stated.Emission.Numeric with
                                            Values = literals |> List.map (fun literal -> literal.Site, literal) |> Map.ofList
                                            ResultSites = literals |> List.map _.Site |> Set.ofList } } }
    let position = Zipper.create graph binding.Id |> require "Missing dispatch witness fixture" |> atChild dispatch.Id
    let accumulator = MLIRAccumulator.empty ()
    let rootScope = ref (ScopeContext.root ())
    let scope = ref (ScopeContext.createChild rootScope.Value FunctionLevel)
    let visited = ref Set.empty
    let ctx: WitnessContext =
        { Coeffects = coeffects 64; Accumulator = accumulator; RootAccumulator = accumulator
          ScopeContext = scope; RootScopeContext = rootScope; Graph = graph; Zipper = position
          GlobalVisited = visited; TraversalVisited = visited }
    let literal (childContext: WitnessContext) (child: SemanticNode) =
        Assert.Equal(child.Id, childContext.Zipper.Focus.Id)
        Assert.NotEmpty(childContext.Zipper.Path)
        Assert.Same(graph, childContext.Graph)
        Alex.Witnesses.LiteralWitness.nanopass.Witness childContext child
    let witness = Alex.Witnesses.ControlFlowWitness.createNanopass (fun () -> literal)
    let output = witness.Witness ctx dispatch
    Assert.Same(graph, ctx.Graph)
    Assert.Same(graph.Nodes, ctx.Graph.Nodes)
    Assert.Same(position.Path, ctx.Zipper.Path)
    Assert.Empty(scope.Value.Operations)
    match output.Result with
    | TRError diagnostic when missingChild ->
        Assert.Equal(Some AX4001, diagnostic.Code)
        Assert.Equal(Some dispatch.Id, diagnostic.NodeId)
        Assert.Equal(Some "graph prerequisites", diagnostic.Phase)
        Assert.Contains($"references missing child {NodeId.value right.Id}", diagnostic.Message)
        Assert.Empty(visited.Value)
    | TRValue value when not missingChild ->
        Assert.Equal<Set<NodeId>>(Set.ofList [selector.Id; left.Id; right.Id], visited.Value)
        let definition = MLIROp.FuncOp(FuncOp.FuncDef("dispatch_witness", [], [value.Type],
            output.InlineOps @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = value.SSA; Type = value.Type }]))], FuncVisibility.Public))
        let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "dispatch_witness" [definition]
        let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
        Assert.Contains("scf.index_switch", verified)
        Assert.Contains("case 0", verified)
    | other -> failwithf "Unexpected dispatch witness result: %A" other

[<Fact>]
let ``empty activation storage has zero extent and admits no slot access`` () =
    let owner = node 0 (SemanticKind.PatternBinding "owner") (sequenceOf boolType) [] None
    let allocation = node 1 (SemanticKind.ContinuationStorage owner.Id) (arrayOf boolType) [] (Some 2)
    let binding = node 2 (SemanticKind.Binding("scratch", false, false, None)) allocation.Type [1] None
    // No Pattern under test reads an emission table of this revision.
    let graph = revision [owner; allocation; binding]
    let position = Zipper.create graph binding.Id |> require "Missing zero activation fixture" |> atChild allocation.Id
    let operands = MLIRAccumulator.empty ()
    let operations, value =
        match observe (pAllocateContinuationStorage allocation.Id 0 1) position operands with
        | Result.Ok ((ops, TRValue result), _) -> ops, result
        | other -> failwithf "Explicit empty activation was rejected: %A" other
    Assert.Equal(TMemRefStatic(0, TInt(IntWidth 8)), value.Type)
    let zero = Alex.Traversal.Values.value binding.Id 0
    let resultType = TInt(IntWidth 32)
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("empty_activation", [], [resultType],
        operations @ [MLIROp.ArithOp(ArithOp.ConstI(zero, 0L, resultType)); MLIROp.FuncOp(FuncOp.Return([{ SSA = zero; Type = resultType }]))], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "empty_activation" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.Contains("memref<0xi8>", verified)
    let pipeline = "builtin.module(expand-strided-metadata,memref-expand,finalize-memref-to-llvm{index-bitwidth=64},convert-index-to-llvm{index-bitwidth=64},convert-func-to-llvm{index-bitwidth=64},convert-arith-to-llvm{index-bitwidth=64},reconcile-unrealized-casts)"
    Alex.Tests.Tools.mlirOpt ["--verify-each"; "--pass-pipeline=" + pipeline] verified |> ignore
    MLIRAccumulator.bindNode allocation.Id value.SSA value.Type operands
    let impossible: ContinuationSlot =
        { Source = owner.Id; ValueType = boolType; Holds = CaptureSlotKind.Scalar SettledSlot.Bool; IsCapture = false
          Field = { Name = "absent"; Slot = SettledSlot.Bool; Offset = Some 0; Size = Some 1; Align = Some 1 } }
    match observe (pReadContinuationSlot binding.Id allocation.Id 0 impossible) position operands with
    | Result.Error message -> Assert.Contains("has no complete placement within its 0-byte frame", message)
    | Result.Ok _ -> failwith "Zero-size activation permitted a slot load"

[<Fact>]
let ``raw caller frame allocation performs no constructor stores`` () =
    let original, plan, allocation, _, _, operands = constructionFixture ()
    let graph = { original.Graph with Nodes = original.Graph.Nodes.Add(allocation, { original.Graph.Nodes[allocation] with Kind = SemanticKind.ContinuationAllocate plan.Owner }) }
    let position = Zipper.create graph original.Focus.Id |> require "Missing caller allocation fixture" |> atChild allocation
    match observe (pAllocateContinuationFrame allocation plan) position operands with
    | Result.Ok (([MLIROp.MemRefOp(MemRefOp.Alloca(ssa, ty, Some 8))], TRValue value), _) ->
        Assert.Equal(value.SSA, ssa)
        Assert.Equal(TMemRefStatic(56, TInt(IntWidth 8)), ty)
        Assert.Equal(ty, value.Type)
    | other -> failwithf "Raw allocation initialized or replaced caller storage: %A" other

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``factory constructor initializes its supplied destination without allocating`` wrongCarrier =
    let original, plan, _, _, _, operands = constructionFixture ()
    let graph = { original.Graph with Codata = { original.Graph.Codata with
                                                    Escapes = Map.empty
                                                    SequenceDestinations = Map.ofList [plan.Owner, plan.Formal] } }
    let position = Zipper.create graph original.Focus.Id |> require "Missing destination fixture" |> atChild plan.Owner
    let frameType = TMemRefStatic((if wrongCarrier then 8 else 56), TInt(IntWidth 8))
    MLIRAccumulator.bindNode plan.Formal (Arg 1) frameType operands
    match observe (pConstructSequence plan.Owner plan plan.Initializers) position operands with
    | Result.Error message when wrongCarrier ->
        Assert.Contains($"Sequence destination {NodeId.value plan.Formal} lacks its settled frame carrier", message)
    | Result.Ok ((operations, TRValue value), _) when not wrongCarrier ->
        Assert.Equal(Arg 1, value.SSA)
        Assert.Equal(frameType, value.Type)
        Assert.DoesNotContain(operations, function MLIROp.MemRefOp(MemRefOp.Alloca _ | MemRefOp.AllocStatic _) -> true | _ -> false)
        let definition = MLIROp.FuncOp(FuncOp.FuncDef("factory_component", [Arg 0, TMemRefStatic(1, TInt(IntWidth 1)); Arg 1, frameType], [value.Type],
            operations @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = value.SSA; Type = value.Type }]))], FuncVisibility.Public))
        let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "factory_component" [definition]
        let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
        Assert.Contains("memref.store", verified)
        Assert.DoesNotContain("memref.alloc", verified)
        let pipeline = "builtin.module(expand-strided-metadata,memref-expand,finalize-memref-to-llvm{index-bitwidth=64},convert-index-to-llvm{index-bitwidth=64},convert-func-to-llvm{index-bitwidth=64},convert-arith-to-llvm{index-bitwidth=64},reconcile-unrealized-casts)"
        Alex.Tests.Tools.mlirOpt ["--verify-each"; "--pass-pipeline=" + pipeline] verified |> ignore
    | other -> failwithf "Unexpected supplied-destination result: %A" other

// The compiler service refuses this fixture for the reason it refuses the construction
// fixture. The nodes the fixture adds carry the numbers its builder gives them. The
// callable rows are those the compiler service publishes for a generator and its formal:
// the alias endpoint of the formal, and its position among the arguments of the generator.
let private ownedRegionFixture () =
    let original, child, first, second, _, operands = constructionFixture ()
    let formalType = pointerTo (sequenceOf boolType)
    let formal = node 14 (SemanticKind.PatternBinding "parentFrame") formalType [] (Some 16)
    // The child sites are the body of the parent generator. A formal is an argument of
    // the function that declares it (Traversal/Values.fs, valuesOf), so a site that
    // views the parent frame through the parent formal lies inside that function. The
    // oracle placed the sites outside it, and the compiler service refuses that fixture.
    let body = { original.Focus with Parent = Some (NodeId 16) }
    let generator =
        node 16 (SemanticKind.Lambda(["parentFrame", formalType, formal.Id], body.Id, [], None, LambdaContext.SeqGenerator))
                (functionFrom formalType boolType) [14; NodeId.value body.Id] None
    let owner = node 17 (SemanticKind.SeqExpr(generator.Id, [])) (sequenceOf boolType) [16] None
    let proof =
        node 18 (SemanticKind.Obligation
                    { Id = "owned_regions_component_layout"; Kind = "continuation-layout"; Logic = "QF_LIA"
                      Statement = "Two distinct child regions occupy the supplied parent extent"
                      Source = "Alex component fixture"; Refs = []
                      Body = ObligationBody.ContinuationLayout([16, 56, 8; 72, 56, 8], 128, 8) }) unitType [] None
    let parent = { child with Owner = owner.Id; Generator = generator.Id; Formal = formal.Id
                              Slots = []; Bytes = 128; Initializers = []; Obligations = [proof.Id] }
    let region offset : ContinuationRegion =
        { ParentOwner = owner.Id; ParentFormal = formal.Id; ChildOwner = child.Owner
          Offset = offset; Bytes = child.Bytes; Alignment = child.Alignment }
    let added = revision [formal; body; generator; owner; proof]
    let nodes = Map.fold (fun nodes id node -> Map.add id node nodes) original.Graph.Nodes added.Nodes
    let graph =
        { original.Graph with
            Nodes = nodes
            Codata = { original.Graph.Codata with
                                Escapes = Map.empty
                                ContinuationFrames = Map.ofList [parent.Owner, parent; child.Owner, child]
                                ContinuationRegions = Map.ofList [first, region 16; second, region 72] }
            Emission = { original.Graph.Emission with
                            Callable = { original.Graph.Emission.Callable with
                                            AliasTargets = Map.ofList [formal.Id, formal.Id]
                                            Arguments = Map.ofList [generator.Id, Map.ofList [formal.Id, [0]]] } } }
    let position =
        Zipper.create graph owner.Id |> require "Missing owned region fixture"
        |> atChild generator.Id |> atChild body.Id
    // A formal has an assigned argument before any source read witnesses it.
    let assigned = Alex.Traversal.Values.resultOf (coeffects 64).TargetPlatform graph [generator.Id] formal.Id
    MLIRAccumulator.registerSSAType assigned (TMemRefStatic(parent.Bytes, TInt(IntWidth 8))) operands
    position, child, first, second, assigned, operands

[<Fact>]
let ``owned child sites view distinct settled parent regions without allocating`` () =
    let position, child, first, second, parentSSA, operands = ownedRegionFixture ()
    let emit id expectedOffset =
        match observe (pAllocateContinuationFrame id child) (position |> atChild id) operands with
        | Result.Ok (([MLIROp.ArithOp(ArithOp.ConstI(offsetSSA, offset, TIndex));
                      MLIROp.MemRefOp(MemRefOp.View(result, source, recalledOffset, sourceType, destinationType))] as operations, TRValue value), _) ->
            Assert.Equal(expectedOffset, offset)
            Assert.Equal(parentSSA, source)
            Assert.Equal(offsetSSA, recalledOffset)
            Assert.Equal(value.SSA, result)
            Assert.Equal(TMemRefStatic(128, TInt(IntWidth 8)), sourceType)
            Assert.Equal(TMemRefStatic(56, TInt(IntWidth 8)), destinationType)
            Assert.Equal(destinationType, value.Type)
            operations, value
        | other -> failwithf "Owned region allocated or lost its settled coordinates: %A" other
    let firstOps, one = emit first 16L
    let secondOps, two = emit second 72L
    Assert.NotEqual(one.SSA, two.SSA)
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("owned_regions_component", [parentSSA, TMemRefStatic(128, TInt(IntWidth 8))], [two.Type],
        firstOps @ secondOps @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = two.SSA; Type = two.Type }]))], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "owned_regions_component" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.DoesNotContain("memref.alloc", verified)
    Assert.DoesNotContain("memref.load", verified)
    let pipeline = "builtin.module(expand-strided-metadata,memref-expand,finalize-memref-to-llvm{index-bitwidth=64},convert-index-to-llvm{index-bitwidth=64},convert-func-to-llvm{index-bitwidth=64},convert-arith-to-llvm{index-bitwidth=64},reconcile-unrealized-casts)"
    Alex.Tests.Tools.mlirOpt ["--verify-each"; "--pass-pipeline=" + pipeline] verified |> ignore

[<Theory>]
[<InlineData(0, "disagrees with its settled child frame")>]
[<InlineData(1, "lacks aligned containment within its parent frame")>]
[<InlineData(2, "lacks aligned containment within its parent frame")>]
let ``owned child regions reject inconsistent child extent alignment and containment`` fault reason =
    let original, child, first, _, _, operands = ownedRegionFixture ()
    let region = original.Graph.Codata.ContinuationRegions[first]
    let malformed =
        match fault with
        | 0 -> { region with Bytes = region.Bytes - 8 }
        | 1 -> { region with Offset = 17 }
        | _ -> { region with Offset = 80 }
    let graph = { original.Graph with Codata = { original.Graph.Codata with
                                                    ContinuationRegions = original.Graph.Codata.ContinuationRegions.Add(first, malformed) } }
    let position = Zipper.create graph original.Focus.Id |> require "Missing rejected region fixture" |> atChild first
    match observe (pAllocateContinuationFrame first child) position operands with
    | Result.Error message -> Assert.Contains($"Continuation region {NodeId.value first} {reason}", message)
    | Result.Ok _ -> failwith "Malformed owned region was accepted"
