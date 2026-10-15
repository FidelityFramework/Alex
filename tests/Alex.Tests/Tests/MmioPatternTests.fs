module Alex.Tests.MmioPatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize
open Alex.Traversal.TransferTypes
open Alex.Tests.Build

/// The opaque handle type of a register of the width given, as the contract states it.
let private handleType (bits: int) : TypeIdentity =
    TypeIdentity.Application(
        { Declaration = { Module = []; Name = sprintf "Mmio%d" bits }; Parameters = []; NativeKind = None }, [])

/// A write of a 16-bit value to an 8-bit register, with the meets published for the write.
/// The handle and the value are formals that were witnessed before the write.
let private registerWrite (meets: Meet list) =
    let handle = node 0 (SemanticKind.PatternBinding "register") (handleType 8) [] None
    let value = node 1 (SemanticKind.PatternBinding "value") intType [] None
    let intrinsic =
        node 2
            (SemanticKind.Intrinsic
                { Module = IntrinsicModule.Mmio; Operation = "write"
                  Category = IntrinsicCategory.Memory; FullName = "Mmio.write" })
            (functionFrom (handleType 8) (functionFrom intType unitType)) [] None
    let write = node 3 (SemanticKind.Application(intrinsic.Id, [handle.Id; value.Id])) unitType [2; 0; 1] None
    let stated = revision [handle; value; intrinsic; write]
    let graph =
        { stated with
            Codata =
                { stated.Codata with
                    Mmio = Map.ofList [ (write.Id, { Operation = "write"; Address = 1073741824I; Bits = 8; Binding = None }) ]
                    Meets = if meets.IsEmpty then Map.empty else Map.ofList [ (write.Id, meets) ] }
            Emission =
                { stated.Emission with
                    Callable =
                        { stated.Emission.Callable with
                            AliasTargets = Map.ofList [ (write.Id, write.Id) ]
                            UnitNodes = Set.singleton write.Id }
                    Numeric =
                        { stated.Emission.Numeric with
                            OccurrenceRepresentations =
                                Map.ofList [ (write.Id, Ok(ValueRepresentation.Scalar SettledSlot.Unit)) ] } } }
        |> declareTraversalReadings
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode handle.Id (Arg 0) TIndex operands
    MLIRAccumulator.bindNode value.Id (Arg 1) (TInt(IntWidth 16)) operands
    graph, focus graph graph.Nodes[write.Id], operands, write.Id, value.Id

[<Fact>]
let ``register write adapts its value by the published meet`` () =
    let truncation consumer operand = { Consumer = consumer; Operand = operand; From = 16; To = 8; Adapt = MeetKind.Truncate }
    let _, position, operands, write, value = registerWrite [ truncation (NodeId 3) (NodeId 1) ]
    match matchAt Alex.Patterns.MmioPatterns.pMmioIntrinsic position 64 operands with
    | Result.Error message -> failwithf "The published meet was not read: %s" message
    | Result.Ok ((operations, result), _) ->
        let adapted = Alex.Traversal.Values.meetValue write 0
        let adaptation =
            operations |> List.choose (function MLIROp.ArithOp(ArithOp.TruncI _ as operation) -> Some operation | _ -> None)
            |> Assert.Single
        Assert.Equal(ArithOp.TruncI(adapted, Arg 1, TInt(IntWidth 16), TInt(IntWidth 8)), adaptation)
        let store =
            operations |> List.choose (function MLIROp.MmioStore(site, stored, address, bits) when site = write -> Some(stored, address, bits) | _ -> None)
            |> Assert.Single
        Assert.Equal((adapted, Arg 0, 8), store)
        // The write is a unit occurrence. No extension is composed.
        Assert.DoesNotContain(operations, fun operation -> match operation with MLIROp.ArithOp(ArithOp.ExtUI _) -> true | _ -> false)
        match result with
        | TRValue unit -> Assert.Equal(TInt(IntWidth 32), unit.Type)
        | other -> failwithf "The write has no unit result: %A" other
    Assert.Equal(Some(Arg 1, TInt(IntWidth 16)), MLIRAccumulator.recallNode value operands)

[<Fact>]
let ``register write without a published meet returns an error and selects no cast`` () =
    let _, position, operands, write, value = registerWrite []
    match matchAt Alex.Patterns.MmioPatterns.pMmioIntrinsic position 64 operands with
    | Result.Error message ->
        Assert.Contains(
            sprintf "Source numeric meet for consumer %d operand %d does not establish destination carrier" (NodeId.value write) (NodeId.value value),
            message)
    | Result.Ok ((operations, _), _) ->
        failwithf "A cast was selected from the widths of the operands: %A" operations
    Assert.Empty(operands.AllOps)
    Assert.Equal(None, MLIRAccumulator.recallNode write operands)

[<Theory>]
[<InlineData("%p = llvm.inttoptr %address : i64 to !llvm.ptr")>]
[<InlineData("llvm.store %v, %p : i8, !llvm.ptr")>]
[<InlineData("\"llvm.mlir.zero\"() : () -> !llvm.ptr")>]
[<InlineData("%p = custom.op : !llvm<\"ptr\">")>]
[<InlineData("\"llvm.store\" // comment\n(%v, %p) : (i8, i64) -> ()")>]
let ``portable serialization refuses LLVM dialect escape fragments`` (text: string) =
    let error = Assert.Throws<System.ArgumentException>(fun () ->
        moduleText (Ok 64) (Some "portable") [MLIROp.RawMLIR text] |> ignore)
    Assert.Contains("ALEX004", error.Message)

[<Theory>]
[<InlineData("func.func private @llvm.libraryFunction()")>]
[<InlineData("func.func private @\"llvm.libraryFunction\"()")>]
[<InlineData("// !llvm.ptr and llvm.load are data here\nfunc.func private @ordinary()")>]
[<InlineData("func.func private @ordinary() attributes {clef.note = \"!llvm.ptr\"}")>]
[<InlineData("func.func private @ordinary() attributes {clef.note = \"llvm.load\"}")>]
let ``portable serialization preserves names comments and quoted data`` (text: string) =
    match moduleText (Ok 64) None [MLIROp.RawMLIR text] with
    | Available actual -> Assert.Equal("module {\n  " + text + "\n}", actual)
    | NeedsTargetRealization -> failwith "Ordinary portable text acquired a target requirement"

let private deferredMmio =
    MLIROp.MmioLoad(NodeId 3, Alex.Traversal.Values.meetValue (NodeId 3) 0, Arg 0, 8)

[<Fact>]
let ``MMIO retains its source intent and explicitly defers target text`` () =
    Assert.Equal(NeedsTargetRealization, moduleText (Ok 64) (Some "portable") [deferredMmio])
    Assert.ThrowsAny<System.Exception>(fun () -> moduleToString (Ok 64) "portable" [deferredMmio] |> ignore)
    |> ignore

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``target deferral cannot mask a later LLVM escape inside a region`` (solver: bool) =
    let poison = MLIROp.RawMLIR "%p = llvm.mlir.zero : !llvm.ptr"
    let nested =
        if solver then MLIROp.SMTOp(SMTSolver [deferredMmio; poison])
        else MLIROp.FuncOp(FuncDef("portable", [Arg 0, TIndex], [], [deferredMmio; poison], FuncVisibility.Public))
    let error = Assert.Throws<System.ArgumentException>(fun () -> moduleText (Ok 64) (Some "portable") [nested] |> ignore)
    Assert.Contains("ALEX004", error.Message)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``portable module headers refuse LLVM syntax before target deferral`` (withMmio: bool) =
    let body = if withMmio then [deferredMmio] else []
    let error = Assert.Throws<System.ArgumentException>(fun () -> moduleText (Ok 64) (Some "unsafe { !llvm.ptr") body |> ignore)
    Assert.Contains("ALEX004", error.Message)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``portable function headers sanitize syntax before target deferral`` (withMmio: bool) =
    let body = if withMmio then [deferredMmio] else []
    let operation = MLIROp.FuncOp(FuncDef("unsafe() -> !llvm.ptr", [], [], body, FuncVisibility.Public))
    match moduleText (Ok 64) (Some "portable") [operation] with
    | Available actual ->
        Assert.False(withMmio)
        Assert.DoesNotContain("!llvm.ptr", actual)
        Assert.Contains("func.func @unsafe_______llvm.ptr(", actual)
    | NeedsTargetRealization -> Assert.True(withMmio)

[<Fact>]
let ``portable headers preserve LLVM named symbols`` () =
    match moduleText (Ok 64) (Some "llvm.library") [MLIROp.RawMLIR "func.func private @llvm.libraryFunction()"] with
    | Available actual -> Assert.Equal("module @llvm.library {\n  func.func private @llvm.libraryFunction()\n}", actual)
    | NeedsTargetRealization -> failwith "A portable module symbol acquired a target requirement"

[<Theory>]
[<InlineData(0, false)>]
[<InlineData(0, true)>]
[<InlineData(8, false)>]
[<InlineData(8, true)>]
let ``target deferral preserves width checking on every portable leaf`` (bits: int, beforeMmio: bool) =
    let conversion = MLIROp.ArithOp(ArithOp.TruncI(Arg 2, Arg 1, TInt(IntWidth 16), TInt(IntWidth bits)))
    let body = if beforeMmio then [conversion; deferredMmio] else [deferredMmio; conversion]
    let operation = MLIROp.FuncOp(FuncDef("portable", [], [], body, FuncVisibility.Public))
    if bits > 0 then
        Assert.Equal(NeedsTargetRealization, moduleText (Ok 64) (Some "portable") [operation])
    else
        let error = Assert.ThrowsAny<System.Exception>(fun () -> moduleText (Ok 64) (Some "portable") [operation] |> ignore)
        Assert.Contains("unresolved or nonpositive integer width", error.Message)

[<Fact>]
let ``portable hardware frame preserves declared argument names`` () =
    let ty = TInt(IntWidth 32)
    let body = [MLIROp.HWOp(HWOutput [Arg 0, ty])]
    let operation = MLIROp.HWOp(HWModule("hardware", ["input", ty], ["output", ty], body))
    Assert.Equal(
        Available "module @portable {\n  hw.module @hardware(in %input: i32, out output: i32) {\n    hw.output %input : i32\n}\n}",
        moduleText (Ok 64) (Some "portable") [operation])
