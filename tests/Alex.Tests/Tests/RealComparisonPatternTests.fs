module Alex.Tests.RealComparisonPatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize
open Alex.Traversal.TransferTypes
open Alex.Tests.Build

let private physicalType = function
    | 32 -> TFloat F32
    | 64 -> TFloat F64
    | bits -> failwithf "Unsupported test format: %d" bits

// This minimal Pattern fixture states only the published rows read here; it
// is not an admitted whole-program revision. Composer tests exercise source
// publication. The runtime formal may be NaN, infinity, zero or finite.
let private comparison bits kind =
    let realType =
        match floatType with
        | TypeIdentity.Numeric(CarrierIdentity.Constructor constructor, dimension) ->
            TypeIdentity.Numeric(CarrierIdentity.Constructor
                { constructor with NativeKind = Some(NTUKind.NTUfloat(NTUWidth.Fixed bits)) }, dimension)
        | _ -> failwith "Expected the fixture's native real type"
    let argument = node 1 (SemanticKind.PatternBinding "value") realType [] None
    let callee = node 2 (SemanticKind.PatternBinding "comparison") unitType [] None
    let call = node 3 (SemanticKind.Application(callee.Id, [argument.Id; argument.Id])) boolType [2; 1] None
    let declaration = node 4 (SemanticKind.Literal NativeLiteral.Unit) unitType [] None
    let participants = Set.ofList [argument.Id; callee.Id; call.Id; declaration.Id]
    let carrier : ScalarCarrier =
        { Site = argument.Id; Slot = SettledSlot.Real bits; Range = ValueRange.Unbounded
          Representation = None; Declaration = Some declaration.Id; SourceType = realType
          Obligations = []; Participants = Set.ofList [argument.Id; declaration.Id] }
    let result : ScalarCarrier =
        { Site = call.Id; Slot = SettledSlot.Bool; Range = ValueRange.Bounded(0I, 1I)
          Representation = None; Declaration = None; SourceType = boolType
          Obligations = []; Participants = Set.singleton call.Id }
    let operand = { Actual = argument.Id; Carrier = Some carrier; Adaptation = None }
    let operation : NumericOperationWitness =
        { Site = call.Id; Callee = callee.Id; Kind = kind; Form = NumericOperationForm.Real
          Operands = [operand; operand]; OperationCarrier = Some(SettledSlot.Real bits)
          Representation = Some { Name = "f" + string bits; Capability = "native"; Family = "ieee"
                                  Bits = bits
                                  MinMagnitude = if bits = 32 then "1.401298464324817e-45" else "4.9406564584124654e-324"
                                  MaxMagnitude = if bits = 32 then "3.4028234663852886e38" else "1.7976931348623157e308"
                                  Boundary = "exact" }
          Declaration = Some declaration.Id; Result = result; ResultAdaptation = None
          Range = None; Obligations = []; Participants = participants }
    let stated = revision [argument; callee; call; declaration]
    let graph =
        { stated with
            Emission =
                { stated.Emission with
                    Callable = { stated.Emission.Callable with AliasTargets = Map.ofList [call.Id, call.Id] }
                    Numeric = { stated.Emission.Numeric with Operations = Map.ofList [call.Id, operation] } } }
        |> declareTraversalReadings
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode argument.Id (Arg 0) (physicalType bits) operands
    let position = focus graph call
    match matchAt (Alex.Patterns.ApplicationPatterns.pNumericOperation call.Id) position 64 operands with
    | Result.Ok ((operations, TRValue value), next) ->
        Assert.Same(graph, next.Graph)
        Assert.Empty(operands.AllOps)
        Assert.Empty(operands.Errors)
        operations |> Assert.Single, value
    | other -> failwithf "Source IEEE comparison was not witnessed: %A" other

[<Theory>]
[<InlineData(32)>]
[<InlineData(64)>]
let ``IEEE self inequality is unordered while self equality remains ordered`` bits =
    // Native type universe section 2.4: x <> x is true for NaN. An ordered
    // not-equal predicate would always make that discriminating case false.
    for kind, predicate, spelling in
        [ NumericOperationKind.NotEqual, FCmpPred.UNe, "une"
          NumericOperationKind.Equal, FCmpPred.OEq, "oeq" ] do
        let operation, value = comparison bits kind
        match operation with
        | MLIROp.ArithOp(ArithOp.CmpF(result, actual, Arg 0, Arg 0, (TFloat _ as operandType))) ->
            Assert.Equal(predicate, actual)
            Assert.Equal(physicalType bits, operandType)
            Assert.Equal(result, value.SSA)
            Assert.Equal(TInt(IntWidth 1), value.Type)
            Assert.Contains("arith.cmpf " + spelling + ",", opToString (Ok 64) operation)
        | other -> failwithf "IEEE comparison changed its exact ordered operands: %A" other
