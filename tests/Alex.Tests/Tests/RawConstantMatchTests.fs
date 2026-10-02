module Alex.Tests.RawConstantMatchTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

let private runOn target inputType inputCarrier patterns =
    let input = node 0 (SemanticKind.PatternBinding "input") inputType [] None
    let bodies = patterns |> List.mapi (fun index _ -> node (index + 1) (SemanticKind.PatternBinding(sprintf "body%d" index)) boolType [] None)
    let arms = List.map2 (fun pattern (body: SemanticNode) -> { Pattern = pattern; Guard = None; Body = body.Id; Bindings = [] }) patterns bodies
    let choice =
        node (List.length patterns + 1) (SemanticKind.CaseElimination(input.Id, arms)) boolType
            [0 .. List.length patterns] None
    // A negative component boundary: raw source syntax has no executable
    // publication. The Pattern must refuse before reading numeric premises.
    // The revision holds the nodes as built and states no emission row.
    let graph = revision (input :: bodies @ [choice]) |> declareTraversalReadings
    let position = Zipper.create graph choice.Id |> require "Missing raw decision"
    let operands = MLIRAccumulator.empty ()
    for index, body in List.indexed bodies do
        MLIRAccumulator.bindNode body.Id (Arg(index + 1)) (TInt(IntWidth 1)) operands
    let parser =
        Alex.Patterns.ControlFlowPatterns.pBuildMatchElimination (Arg 0) inputCarrier input.Id
            (arms |> List.map (fun arm -> [], arm.Body, arm))
            (Some(Alex.Traversal.Values.value choice.Id 0, TInt(IntWidth 1))) choice.Id
    Alex.XParsec.PSGCombinators.tryMatchWithDiagnostics parser graph position.Focus position
        { coeffects 64 with TargetPlatform = target } operands

let private run inputType inputCarrier patterns = runOn Alex.Target.CPU inputType inputCarrier patterns

[<Theory>]
[<InlineData("bool")>]
[<InlineData("int64")>]
[<InlineData("uint64")>]
let ``raw constants require source normalization even when their scalar values fit on fabric`` category =
    let inputType, carrier, literal =
        match category with
        | "bool" -> boolType, TInt(IntWidth 1), NativeLiteral.Bool true
        | "int64" ->
            let value = (1L <<< 40) + 3L
            intType, TInt(IntWidth 64), NativeLiteral.Int(value, NTUKind.NTUint(NTUWidth.Fixed 64))
        | _ -> intType, TInt(IntWidth 64), NativeLiteral.UInt(System.UInt64.MaxValue, NTUKind.NTUuint(NTUWidth.Fixed 64))
    match runOn Alex.Target.FPGA inputType carrier [Pattern.Const literal; Pattern.Wildcard] with
    | Result.Error reason -> Assert.Contains("typed equality and conditional normalization", reason)
    | other -> failwithf "Raw scalar match was interpreted by a witness: %A" other

[<Theory>]
[<InlineData("bool")>]
[<InlineData("int")>]
let ``raw constants require source normalization even with an explicit final default`` category =
    let inputType, inputCarrier, literal =
        if category = "bool" then boolType, TInt(IntWidth 1), NativeLiteral.Bool true
        else intType, TInt(IntWidth 16), NativeLiteral.Int(937L, NTUKind.NTUint(NTUWidth.Fixed 64))
    match run inputType inputCarrier [Pattern.Const literal; Pattern.Wildcard] with
    | Result.Error reason -> Assert.Contains("typed equality and conditional normalization", reason)
    | other -> failwithf "Raw scalar match was interpreted by a witness: %A" other

[<Theory>]
[<InlineData("char")>]
[<InlineData("float")>]
[<InlineData("string")>]
[<InlineData("unit")>]
[<InlineData("missing-default")>]
[<InlineData("early-default")>]
[<InlineData("mixed-constant-category")>]
[<InlineData("wrong-input-type")>]
[<InlineData("wrong-carrier")>]
[<InlineData("integer-overflow")>]
[<InlineData("negative-literal-unsigned-carrier")>]
[<InlineData("multiple-record-arms")>]
[<InlineData("multiple-tuple-arms")>]
let ``raw constant decisions reject missing source settlement instead of using positional labels`` defect =
    let boolean = Pattern.Const(NativeLiteral.Bool true)
    let inputType, carrier, patterns =
        match defect with
        | "char" -> charType, TInt(IntWidth 32), [Pattern.Const(NativeLiteral.Char 'Ω'); Pattern.Wildcard]
        | "float" -> floatType, TFloat F64, [Pattern.Const(NativeLiteral.Float(1.5, NTUKind.NTUfloat(NTUWidth.Fixed 64))); Pattern.Wildcard]
        | "string" -> stringType, TMemRef(TInt(IntWidth 8)), [Pattern.Const(NativeLiteral.String "same"); Pattern.Wildcard]
        | "unit" -> unitType, TInt(IntWidth 32), [Pattern.Const NativeLiteral.Unit; Pattern.Wildcard]
        | "missing-default" -> boolType, TInt(IntWidth 1), [boolean; Pattern.Const(NativeLiteral.Bool false)]
        | "early-default" -> boolType, TInt(IntWidth 1), [Pattern.Wildcard; boolean; Pattern.Wildcard]
        | "mixed-constant-category" -> boolType, TInt(IntWidth 1), [boolean; Pattern.Const(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 64))); Pattern.Wildcard]
        | "wrong-input-type" -> charType, TInt(IntWidth 1), [boolean; Pattern.Wildcard]
        | "integer-overflow" -> intType, TInt(IntWidth 16), [Pattern.Const(NativeLiteral.Int(70000L, NTUKind.NTUint(NTUWidth.Fixed 64))); Pattern.Wildcard]
        | "negative-literal-unsigned-carrier" -> intType, TInt(IntWidth 16), [Pattern.Const(NativeLiteral.Int(-1L, NTUKind.NTUint(NTUWidth.Fixed 64))); Pattern.Wildcard]
        | "multiple-record-arms" ->
            let recordType = TypeIdentity.AnonymousRecord(false, [("Value", boolType)])
            recordType, TMemRef(TInt(IntWidth 8)), [Pattern.Record([], recordType); Pattern.Wildcard]
        | "multiple-tuple-arms" ->
            TypeIdentity.Tuple(false, [boolType]), TMemRef(TInt(IntWidth 8)), [Pattern.Tuple [Pattern.Wildcard]; Pattern.Wildcard]
        | _ -> boolType, TInt(IntWidth 32), [boolean; Pattern.Wildcard]
    match run inputType carrier patterns with
    | Result.Error _ -> ()
    | other -> failwithf "Raw constant decision invented settlement for %s: %A" defect other
