module Alex.Tests.MmioPatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
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
            operations |> List.choose (function MLIROp.MmioStore(stored, address, _, _, bits) -> Some(stored, address, bits) | _ -> None)
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
