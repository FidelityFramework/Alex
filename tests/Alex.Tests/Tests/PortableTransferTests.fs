module Alex.Tests.PortableTransferTests

open System
open System.Globalization
open System.Text
open System.Text.RegularExpressions
open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize
open Alex.Traversal.TransferTypes

[<Fact>]
let ``trace snapshots preserve append order and monotonic timestamps`` () =
    let collector = TraceCollector.create ()
    TraceCollector.add 0 "witness" (Some(NodeId 4)) "first" collector
    let snapshot = TraceCollector.toList collector
    TraceCollector.add 1 "pattern" None "second" collector
    TraceCollector.add 2 "element" None "third" collector
    Assert.Equal<int list>([0; 1; 2], TraceCollector.toList collector |> List.map _.Timestamp)
    Assert.Equal<string list>(["first"; "second"; "third"], TraceCollector.toList collector |> List.map _.Parameters)
    Assert.Equal<string list>(["first"], snapshot |> List.map _.Parameters)

[<Fact>]
let ``attribute encoding preserves all UTF8 bytes and refuses unpaired surrogates`` () =
    let value = "quote\" slash\\ nul\000 newline\n é 水 😀"
    let expected =
        UTF8Encoding(false, true).GetBytes value
        |> Array.map (fun b -> if b >= 32uy && b <= 126uy && b <> 34uy && b <> 92uy then string (char b) else sprintf "\\%02X" b)
        |> String.concat ""
    Assert.Equal("cf.assert %arg0, \"" + expected + "\"", opToString (Ok 64) (MLIROp.Assert(Arg 0, value)))
    let high, low = String([|char 0xD800|]), String([|char 0xDC00|])
    for malformed in [high; low; high + "x"; "x" + low] do
        Assert.ThrowsAny<Exception>(fun () -> opToString (Ok 64) (MLIROp.Assert(Arg 0, malformed)) |> ignore) |> ignore

let private floatArray value =
    let authority: MemoryArrayLiteralWitness =
        { Site = NodeId 0; Elements = [NodeId 1, None]; Element = SettledSlot.Real 64
          Length = 1; Residence = MemoryResidence.ImmutableProgram(NodeId 2)
          Initializers = Some [NativeLiteral.Float(value, NTUKind.NTUfloat(NTUWidth.Fixed 64))]
          Alignment = 8; ElementBytes = 8; Participants = Set.ofList [NodeId 0; NodeId 1; NodeId 2] }
    GlobalArray("values", TMemRefStatic(1, TFloat F64), authority)

[<Fact>]
let ``immutable floating initializers round trip every bit independent of culture`` () =
    let random = Random 1713
    let values =
        [ yield! [0.0; -0.0; Double.Epsilon; -Double.Epsilon; Double.MaxValue; Double.MinValue; Math.PI; 0.1]
          for _ in 1 .. 1000 do
              let bytes = Array.zeroCreate<byte> 8
              random.NextBytes bytes
              let value = BitConverter.ToDouble bytes
              if Double.IsFinite value then yield value ]
    let previous = CultureInfo.CurrentCulture
    try
        for culture in ["en-US"; "fr-FR"; "ar-SA"] do
            CultureInfo.CurrentCulture <- CultureInfo.GetCultureInfo culture
            for value in values do
                let text = opToString (Ok 64) (floatArray value)
                let token = Regex.Match(text, @"dense<\[([^\]]+)\]>").Groups[1].Value
                let parsed = Double.Parse(token, CultureInfo.InvariantCulture)
                Assert.Equal(BitConverter.DoubleToInt64Bits value, BitConverter.DoubleToInt64Bits parsed)
        for value in [Double.NaN; Double.PositiveInfinity; Double.NegativeInfinity] do
            Assert.ThrowsAny<Exception>(fun () -> opToString (Ok 64) (floatArray value) |> ignore) |> ignore
    finally CultureInfo.CurrentCulture <- previous

[<Fact>]
let ``integer serialization retains mathematical values beyond signed machine range`` () =
    let previous = CultureInfo.CurrentCulture
    try
        CultureInfo.CurrentCulture <- CultureInfo.GetCultureInfo "ar-SA"
        for value in [-18446744073709551615I; -9223372036854775808I; 0I; 18446744073709551615I] do
            let operation = ArithOp(ArithOp.ConstI(Arg 0, value, TInt(IntWidth 128)))
            let expected = value.ToString(CultureInfo.InvariantCulture)
            Assert.Equal("%arg0 = arith.constant " + expected + " : i128", opToString (Ok 64) operation)
    finally CultureInfo.CurrentCulture <- previous

[<Fact>]
let ``blank published identities retain Unicode whitespace refusal`` () =
    for code in 0 .. 65535 do
        Assert.Equal(Char.IsWhiteSpace(char code), Alex.Text.isBlank (string (char code)))
    Assert.True(Alex.Text.isBlank null)
    Assert.True(Alex.Text.isBlank "")
    Assert.False(Alex.Text.isBlank " x ")

[<Fact>]
let ``XDC emits ordered pin groups with portable newlines and refuses unknown directions`` () =
    let pin name direction = { PortName = name; PackagePin = "A1"; IOStandard = "LVCMOS33"; Direction = direction }
    let mapping: PinMapping =
        { Pins = [pin "out" "Output"; pin "in1" "Input"; pin "io" "InOut"; pin "in2" "Input"]
          Clock = { PortName = "clk"; PackagePin = "B1"; IOStandard = "LVCMOS33"; FrequencyHz = 100_000_000L }
          Reset = None; DevicePart = "fixture"; FieldPinAttrs = Map.empty }
    let text = Alex.Traversal.XDCTransfer.transfer mapping |> Result.defaultWith failwith
    Assert.DoesNotContain("\r", text)
    Assert.False(text.EndsWith "\n")
    Assert.Contains("-period 10.000", text)
    let ordered = ["# Inputs"; "{in1}"; "{in2}"; "# Outputs"; "{out}"; "# Bidirectional"; "{io}"] |> List.map text.IndexOf
    Assert.True(ordered |> List.forall (fun index -> index >= 0))
    Assert.Equal<int list>(List.sort ordered, ordered)
    match Alex.Traversal.XDCTransfer.transfer { mapping with Pins = pin "bad" "Unknown" :: mapping.Pins } with
    | Result.Error reason -> Assert.Contains("bad (direction 'Unknown')", reason)
    | Result.Ok _ -> failwith "Unsettled pin was silently emitted"

[<Fact>]
let ``SMT comparisons retain constants before uses and the complete ordered anchor`` () =
    let obligation: ObligationInfo =
        { Id = "range-proof"; Kind = "test"; Logic = "QF_LIA"; Statement = "range"; Source = "fixture"
          Refs = []; Body = ObligationBody.IntegerRepresentationCoverage(2I, 4I, 0I, 9I) }
    let solver =
        Alex.Traversal.SMTTransfer.operations [obligation]
        |> List.choose (function SMTOp(SMTSolver body) -> Some body | _ -> None)
        |> Assert.Single
    let s n = V(0, n)
    let expected =
        [ SMTSetLogic "QF_LIA"
          SMTBigIntConstant(s 0, 0I); SMTBigIntConstant(s 1, 2I); SMTIntCmp(s 2, SmtLe, s 0, s 1)
          SMTBigIntConstant(s 3, 2I); SMTBigIntConstant(s 4, 4I); SMTIntCmp(s 5, SmtLe, s 3, s 4)
          SMTBigIntConstant(s 6, 4I); SMTBigIntConstant(s 7, 9I); SMTIntCmp(s 8, SmtLe, s 6, s 7)
          SMTAnd(s 9, [s 2; s 5; s 8]); SMTDeclareFun(s 10, "range-proof", SMTBool)
          SMTEq(s 11, s 10, s 9, SMTBool); SMTAssert(s 11); SMTNot(s 12, s 10); SMTAssert(s 12); SMTCheck ]
        |> List.map SMTOp
    Assert.Equal<MLIROp list>(expected, solver)
