/// One array read, stated as a revision, with the operands its Pattern recalls.
module Alex.Tests.ArrayRead

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

/// Component-boundary fixture, not a source program or a substitute for Baker.
/// The index already has its analysed range and an i8 operand representation.
/// Neither this fixture nor the tested pattern establishes array bounds.
type ArrayRead =
    { Graph: Revision
      Binding: NodeId
      Lambda: NodeId
      Array: NodeId
      Index: NodeId
      Call: NodeId
      Proof: NodeId
      Position: Zipper.PSGZipper }

// The fixture declares no bound of the array. The access row of the contract has
// fields for a bound, and pIndexGetArray reads none of them. Each such field holds
// a value that names no node of the revision and no scalar form.
let private notStated = NodeId -1

let private boundNotStated : ScalarCarrier =
    { Site = notStated
      Slot = SettledSlot.Opaque "The fixture states no extent of the array."
      Range = ValueRange.Unbounded
      Representation = None
      Declaration = None
      SourceType = TypeIdentity.Error "The fixture states no extent of the array."
      Obligations = []
      Participants = Set.empty }

let private requirementNotStated : RequirementWitness =
    { Site = notStated
      Condition = notStated
      Diagnostic = "The fixture states no bound requirement."
      Frontier = notStated
      Continuation = notStated
      PatternTest = None
      Participants = [] }

let arrayRead unsigned =
    let arrayType = arrayOf boolType
    let readType = functionFrom arrayType (functionFrom intType boolType)
    let lower, upper = if unsigned then 128I, 255I else -128I, 127I
    let minimum, maximum = if unsigned then 0I, 255I else -128I, 127I
    let array = node 0 (SemanticKind.PatternBinding "values") arrayType [] (Some 4)
    let index =
        { node 1 (SemanticKind.PatternBinding "index") intType [] (Some 4) with
            ValueRange = Some (ValueRange.Bounded(lower, upper)) }
    let intrinsic =
        node 2
            (SemanticKind.Intrinsic
                { Module = IntrinsicModule.Array; Operation = "get"
                  Category = IntrinsicCategory.Memory; FullName = "Array.get" })
            readType [] None
    let call = node 3 (SemanticKind.Application(intrinsic.Id, [array.Id; index.Id])) boolType [2; 0; 1] (Some 4)
    let lambda =
        node 4
            (SemanticKind.Lambda(["values", arrayType, array.Id; "index", intType, index.Id],
                                 call.Id, [], None, LambdaContext.RegularClosure))
            readType [0; 1; 3] (Some 5)
    let binding = node 5 (SemanticKind.Binding("read", false, false, None)) readType [4] None
    let proof =
        node 6
            (SemanticKind.Obligation
                { Id = "index_carrier"; Kind = "integer-representation-coverage"; Logic = "QF_LIA"
                  Statement = "The supplied index range fits its supplied operand carrier"
                  Source = "Alex component fixture"; Refs = []
                  Body = ObligationBody.IntegerRepresentationCoverage(lower, upper, minimum, maximum) })
            unitType [] None
    // The carrier of the index: eight bits, the analysed range, and the obligation
    // that the range fits the carrier.
    let indexCarrier : ScalarCarrier =
        { Site = index.Id
          Slot = SettledSlot.Integer(8, None)
          Range = ValueRange.Bounded(lower, upper)
          Representation = None
          Declaration = None
          SourceType = intType
          Obligations = [ proof.Id ]
          Participants = Set.singleton index.Id }
    let bounds : MemoryBoundsWitness =
        { Buffer = array.Id
          Index = index.Id
          IndexCarrier = indexCarrier
          ExtentCarrier = boundNotStated
          IndexUnsigned = unsigned
          Length = notStated
          Lower = notStated
          Upper = notStated
          Requirement = requirementNotStated
          Participants = Set.ofList [ array.Id; index.Id ] }
    // The access contract that pIndexGetArray reads at the call. The element is a bool.
    let access : MemoryArrayAccessWitness =
        { Site = call.Id
          Buffer = array.Id
          Index = index.Id
          Value = None
          Element = SettledSlot.Bool
          Adaptation = None
          Bounds = bounds
          Participants = Set.ofList [ array.Id; index.Id; call.Id ] }
    let stated = revision [ array; index; intrinsic; call; lambda; binding; proof ]
    let graph =
        { stated with
            Edges =
                [ { Sources = [ index.Id ]; Target = proof.Id; Class = EdgeClass.Obligation
                    Role = EdgeRole.Constrains; Ordinal = 0 } ]
            Emission =
                { stated.Emission with
                    Callable =
                        { stated.Emission.Callable with
                            // The values of the call are named from the call itself.
                            AliasTargets = Map.ofList [ (call.Id, call.Id) ] }
                    Memory =
                        { stated.Emission.Memory with
                            Operations = Map.ofList [ (call.Id, MemoryWitnessOperation.ArrayAccess access) ] } } }
        |> declareTraversalReadings
    let position =
        Zipper.create graph binding.Id |> require "Missing fixture binding"
        |> atChild lambda.Id |> atChild call.Id
    { Graph = graph; Binding = binding.Id; Lambda = lambda.Id; Array = array.Id
      Index = index.Id; Call = call.Id; Proof = proof.Id; Position = position }

/// The current public parser API requires a table of already witnessed operands.
/// Seed those two inputs only; tests do not run or reproduce the mutable traversal.
let recalledOperands fixture =
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode fixture.Array (Arg 0) (TMemRef(TInt(IntWidth 1))) operands
    MLIRAccumulator.bindNode fixture.Index (Arg 1) (TInt(IntWidth 8)) operands
    operands

let readArray fixture pointerBits operands =
    match matchAt Alex.Patterns.MemoryPatterns.pIndexGetArray fixture.Position pointerBits operands with
    | Result.Ok ((operations, result), position) -> operations, result, position
    | Result.Error message -> failwith message

let readModule fixture pointerBits =
    let operations, result, _ = readArray fixture pointerBits (recalledOperands fixture)
    match result with
    | TRValue value ->
        let body = operations @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = value.SSA; Type = value.Type }]))]
        let definition = MLIROp.FuncOp(FuncOp.FuncDef(
            "read_index", [Arg 0, TMemRef(TInt(IntWidth 1)); Arg 1, TInt(IntWidth 8)], [value.Type], body, FuncVisibility.Public))
        Alex.Dialects.Core.Serialize.moduleToString (Ok pointerBits) "index_component" [definition]
    | other -> failwithf "Array.get did not produce a value: %A" other
