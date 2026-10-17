/// MLIR Serialization
///
/// Converts structured MLIR types and operations to MLIR text format.
/// This is the ONLY place where sprintf is used for MLIR text generation.
/// All upstream code (witnesses, patterns, elements) works with structured MLIROp.
module Alex.Dialects.Core.Serialize

open Alex.Dialects.Core.Types

/// Text escapes remain portable. Quoted data, symbols and comments are not
/// dialect operations; a quoted generic operation is identified by its operands.
let private portableTokens =
    System.Text.RegularExpressions.Regex(
        "(?<comment>//[^\\r\\n]*)|(?<symbol>@(?:\"(?:\\\\[\\s\\S]|[^\"])*\"|[A-Za-z_][A-Za-z0-9_$.]*))|(?<quoted>\"(?:\\\\[\\s\\S]|[^\"])*\")|(?<backend>!llvm(?=[.<])|(?<![\\w$.])llvm\\.[A-Za-z_][A-Za-z0-9_.]*)|(?<other>[^\\s])")

let private portableText (text: string) =
    let refuse () = invalidArg "text" "ALEX004: LLVM dialect constructs belong to backend realization, never Alex portable output."
    portableTokens.Matches text
    |> Seq.cast<System.Text.RegularExpressions.Match>
    |> Seq.fold (fun quotedOperation token ->
        if token.Groups.["comment"].Success then quotedOperation
        else
            if token.Groups.["backend"].Success || (quotedOperation && token.Value = "(") then refuse ()
            token.Groups.["quoted"].Success
            && System.Text.RegularExpressions.Regex.IsMatch(token.Value, "^\"llvm\\.[A-Za-z_][A-Za-z0-9_.]*\"$")) false
    |> ignore
    text

exception private TargetRealizationRequired of string

/// MLIR symbol names are bare identifiers ([A-Za-z_][A-Za-z0-9_$.]*). A Clef function name may
/// carry an apostrophe (`process'`), which is legal in F# and in the linked ELF symbol but not
/// in a bare MLIR id; it is spelled `$` in the symbol (a character no Clef name contains).
let symbolName (name: string) : string =
    name |> String.map (fun c -> if c = '\'' then '$' elif System.Char.IsLetterOrDigit c || c = '_' || c = '.' || c = '$' then c else '_')

/// MLIR string attributes carry bytes. Escape non-printable and non-ASCII UTF8
/// bytes as two hexadecimal digits, preserving embedded NUL and line breaks.
let private stringAttributeValue (value: string) =
    System.Text.UTF8Encoding(false, true).GetBytes(value)
    |> Array.map (fun value ->
        if value >= 32uy && value <= 126uy && value <> 34uy && value <> 92uy then string (char value)
        else sprintf "\\%02X" value)
    |> String.concat ""


// ═══════════════════════════════════════════════════════════════════════════
// TYPE SERIALIZATION
// ═══════════════════════════════════════════════════════════════════════════

/// Spell an exact positive source-published integer width.
let intWidthToString (IntWidth bits) : string =
    if bits <= 0 then
        failwith "An unresolved or nonpositive integer width reached serialization; a complete source-published representation is required."
    sprintf "i%d" bits

/// Convert FloatWidth to MLIR type string
let floatWidthToString (width: FloatWidth) : string =
    match width with
    | F32 -> "f32"
    | F64 -> "f64"

/// Convert MLIRType to MLIR text format string
let rec typeToString (pointer: Result<int, string>) (ty: MLIRType) : string =
    match ty with
    | TOpaqueHandle _ | TResourceOption _ ->
        raise (TargetRealizationRequired "Opaque resource carriers require the selected backend and their exact source accounts.")
    | TInt width -> intWidthToString width
    | TFloat width -> floatWidthToString width
    | TFunc (paramTypes, resultTypes) ->
        let paramStrs = paramTypes |> List.map (typeToString pointer) |> String.concat ", "
        sprintf "(%s) -> %s" paramStrs (resultTypesToString pointer resultTypes)
    | TMemRef elemTy ->
        sprintf "memref<?x%s>" (typeToString pointer elemTy)
    | TMemRefStatic (size, elemTy) ->
        sprintf "memref<%dx%s>" size (typeToString pointer elemTy)
    | TMemRefScalar elemTy ->
        sprintf "memref<%s>" (typeToString pointer elemTy)
    | TVector (count, elemTy) ->
        sprintf "vector<%dx%s>" count (typeToString pointer elemTy)
    | TIndex -> "index"
    | TVoid -> "()"  // Empty MLIR result list at a foreign function boundary
    | TStruct (_, Some bytes) ->
        // TStruct serializes as !hw.struct for CIRCT (FPGA) or memref for CPU.
        // This default path is CPU; hwTypeToString pointer handles the FPGA case.
        // The byte size is the settled layout's, read from the graph (the one size model).
        sprintf "memref<%dxi8>" bytes.Size
    | TStruct (fields, None) ->
        failwithf "typeToString: the struct {%s} reached serialization on a core with no settled layout" (fields |> List.map fst |> String.concat ", ")
    | TSeqClock -> "!seq.clock"
    | TTag caseCount ->
        // Default serialization: smallest power-of-2 integer that fits the case count
        // Platform-specific serializers (hw dialect) may override with exact bit widths
        if caseCount <= 2 then "i1"
        elif caseCount <= 256 then "i8"
        elif caseCount <= 65536 then "i16"
        else "i32"

/// Function results are a list. A sole function-typed result still needs the
/// enclosing result-list parentheses so its own arrow is unambiguous.
and resultTypesToString (pointer: Result<int, string>) (results: MLIRType list) : string =
    if List.contains TVoid results then
        failwith "Function result lists use [] for no result; TVoid is not a value type"
    match results with
    | [result] when (match result with TFunc _ -> false | _ -> true) -> typeToString pointer result
    | _ -> results |> List.map (typeToString pointer) |> String.concat ", " |> sprintf "(%s)"

/// FPGA-aware type serialization: TStruct → !hw.struct<...>, all others → typeToString pointer
/// Used by comb.* and other CIRCT ops that carry struct types on FPGA.
let rec hwTypeToString (pointer: Result<int, string>) (ty: MLIRType) : string =
    match ty with
    | TStruct (fields, _) ->
        let fs = fields |> List.map (fun (n, t) -> sprintf "%s: %s" n (hwTypeToString pointer t))
        sprintf "!hw.struct<%s>" (String.concat ", " fs)
    | _ -> typeToString pointer ty

// ═══════════════════════════════════════════════════════════════════════════
// SSA SERIALIZATION
// ═══════════════════════════════════════════════════════════════════════════

/// Convert SSA to MLIR SSA value string
let ssaToString (ssa: SSA) : string =
    match ssa with
    | V (n, k) -> sprintf "%%v%d_%d" n k
    | CallableAlternative (n, alternative) -> sprintf "%%callable_%d_alternative_%d" n alternative
    | AggregateComponent (n, slot, alternative, lane) -> sprintf "%%aggregate_%d_slot_%d_alternative_%d_lane_%d" n slot alternative lane
    | ArrayElementIndex (n, element) -> sprintf "%%array_%d_element_%d" n element
    | Arg n -> sprintf "%%arg%d" n

/// Convert Val (SSA + type) to typed SSA value string
let valToString (pointer: Result<int, string>) (v: Val) : string =
    sprintf "%s : %s" (ssaToString v.SSA) (typeToString pointer v.Type)

let private resultAssignment (results: Val list) =
    match results with
    | [] -> ""
    | _ -> (results |> List.map (fun value -> ssaToString value.SSA) |> String.concat ", ") + " = "

// ═══════════════════════════════════════════════════════════════════════════
// OPERATION SERIALIZATION
// ═══════════════════════════════════════════════════════════════════════════

/// Convert ICmpPred to MLIR predicate string
let icmpPredToString (pred: ICmpPred) : string =
    match pred with
    | ICmpPred.Eq -> "eq"
    | ICmpPred.Ne -> "ne"
    | ICmpPred.Slt -> "slt"
    | ICmpPred.Sle -> "sle"
    | ICmpPred.Sgt -> "sgt"
    | ICmpPred.Sge -> "sge"
    | ICmpPred.Ult -> "ult"
    | ICmpPred.Ule -> "ule"
    | ICmpPred.Ugt -> "ugt"
    | ICmpPred.Uge -> "uge"

/// Convert FCmpPred to MLIR predicate string
let fcmpPredToString (pred: FCmpPred) : string =
    match pred with
    | OEq -> "oeq"
    | OGt -> "ogt"
    | OGe -> "oge"
    | OLt -> "olt"
    | OLe -> "ole"
    | ONe -> "one"
    | Ord -> "ord"
    | UEq -> "ueq"
    | UGt -> "ugt"
    | UGe -> "uge"
    | ULt -> "ult"
    | ULe -> "ule"
    | UNe -> "une"
    | Uno -> "uno"
    | AlwaysFalse -> "false"
    | AlwaysTrue -> "true"

/// Serialize ArithOp to MLIR text
let arithOpToString (pointer: Result<int, string>) (op: ArithOp) : string =
    match op with
    | ConstI (result, value, ty) ->
        sprintf "%s = arith.constant %d : %s" (ssaToString result) value (typeToString pointer ty)
    | ConstF (result, value, ty) ->
        sprintf "%s = arith.constant %f : %s" (ssaToString result) value (typeToString pointer ty)
    | AddI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.addi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | SubI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.subi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | MulI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.muli %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | DivSI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.divsi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | DivUI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.divui %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | RemSI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.remsi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | RemUI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.remui %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | AddF (result, lhs, rhs, ty) ->
        sprintf "%s = arith.addf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | SubF (result, lhs, rhs, ty) ->
        sprintf "%s = arith.subf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | NegF (result, operand, ty) ->
        sprintf "%s = arith.negf %s : %s" (ssaToString result) (ssaToString operand) (typeToString pointer ty)
    | MulF (result, lhs, rhs, ty) ->
        sprintf "%s = arith.mulf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | DivF (result, lhs, rhs, ty) ->
        sprintf "%s = arith.divf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | CmpI (result, pred, lhs, rhs, ty) ->
        sprintf "%s = arith.cmpi %s, %s, %s : %s" (ssaToString result) (icmpPredToString pred) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | CmpF (result, pred, lhs, rhs, ty) ->
        sprintf "%s = arith.cmpf %s, %s, %s : %s" (ssaToString result) (fcmpPredToString pred) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | ExtSI (result, value, srcTy, destTy) ->
        sprintf "%s = arith.extsi %s : %s to %s" (ssaToString result) (ssaToString value) (typeToString pointer srcTy) (typeToString pointer destTy)
    | ExtUI (result, value, srcTy, destTy) ->
        sprintf "%s = arith.extui %s : %s to %s" (ssaToString result) (ssaToString value) (typeToString pointer srcTy) (typeToString pointer destTy)
    | ExtF (result, value, srcTy, destTy) ->
        sprintf "%s = arith.extf %s : %s to %s" (ssaToString result) (ssaToString value) (typeToString pointer srcTy) (typeToString pointer destTy)
    | TruncF (result, value, srcTy, destTy) ->
        sprintf "%s = arith.truncf %s : %s to %s" (ssaToString result) (ssaToString value) (typeToString pointer srcTy) (typeToString pointer destTy)
    | TruncI (result, value, srcTy, destTy) ->
        sprintf "%s = arith.trunci %s : %s to %s" (ssaToString result) (ssaToString value) (typeToString pointer srcTy) (typeToString pointer destTy)
    | SIToFP (result, value, srcTy, destTy) ->
        sprintf "%s = arith.sitofp %s : %s to %s" (ssaToString result) (ssaToString value) (typeToString pointer srcTy) (typeToString pointer destTy)
    | FPToSI (result, value, srcTy, destTy) ->
        sprintf "%s = arith.fptosi %s : %s to %s" (ssaToString result) (ssaToString value) (typeToString pointer srcTy) (typeToString pointer destTy)
    | Select (result, cond, trueVal, falseVal, ty) ->
        sprintf "%s = arith.select %s, %s, %s : %s"
            (ssaToString result) (ssaToString cond) (ssaToString trueVal) (ssaToString falseVal) (typeToString pointer ty)
    // Bitwise operations (migrated from LLVM dialect)
    | AndI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.andi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | OrI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.ori %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | XorI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.xori %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | ShLI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.shli %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | ShRUI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.shrui %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)
    | ShRSI (result, lhs, rhs, ty) ->
        sprintf "%s = arith.shrsi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (typeToString pointer ty)

/// Serialize CombOp to CIRCT MLIR text (comb dialect)
/// Uses hwTypeToString: comb.* ops only appear on FPGA where TStruct → !hw.struct
let combOpToString (pointer: Result<int, string>) (op: CombOp) : string =
    match op with
    | CombAdd (result, lhs, rhs, ty) ->
        sprintf "%s = comb.add %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombSub (result, lhs, rhs, ty) ->
        sprintf "%s = comb.sub %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombMul (result, lhs, rhs, ty) ->
        sprintf "%s = comb.mul %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombDivS (result, lhs, rhs, ty) ->
        sprintf "%s = comb.divs %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombDivU (result, lhs, rhs, ty) ->
        sprintf "%s = comb.divu %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombMod (result, lhs, rhs, ty) ->
        sprintf "%s = comb.mods %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombModU (result, lhs, rhs, ty) ->
        sprintf "%s = comb.modu %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombAnd (result, lhs, rhs, ty) ->
        sprintf "%s = comb.and %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombOr (result, lhs, rhs, ty) ->
        sprintf "%s = comb.or %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombXor (result, lhs, rhs, ty) ->
        sprintf "%s = comb.xor %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombShl (result, lhs, rhs, ty) ->
        sprintf "%s = comb.shl %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombShrU (result, lhs, rhs, ty) ->
        sprintf "%s = comb.shru %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombShrS (result, lhs, rhs, ty) ->
        sprintf "%s = comb.shrs %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombICmp (result, pred, lhs, rhs, ty) ->
        sprintf "%s = comb.icmp %s %s, %s : %s" (ssaToString result) (icmpPredToString pred) (ssaToString lhs) (ssaToString rhs) (hwTypeToString pointer ty)
    | CombMux (result, cond, trueVal, falseVal, ty) ->
        sprintf "%s = comb.mux %s, %s, %s : %s" (ssaToString result) (ssaToString cond) (ssaToString trueVal) (ssaToString falseVal) (hwTypeToString pointer ty)

/// Serialize HWOp to CIRCT MLIR text (hw dialect)
/// Hardware module containers use the neutral frame grammar below.
let hwOpToString (pointer: Result<int, string>) (op: HWOp) : string =
    match op with
    | HWModule _ -> invalidOp "Hardware module serialization requires its neutral container frame."
    | HWOutput vals ->
        match vals with
        | [] -> "hw.output"
        | _ ->
            let valsStr = vals |> List.map (fun (ssa, _) -> ssaToString ssa) |> String.concat ", "
            let typesStr = vals |> List.map (fun (_, ty) -> hwTypeToString pointer ty) |> String.concat ", "
            sprintf "hw.output %s : %s" valsStr typesStr
    | HWStructCreate (result, fieldVals, structTy) ->
        let valsStr = fieldVals |> List.map (fun (ssa, _) -> ssaToString ssa) |> String.concat ", "
        let tyStr = hwTypeToString pointer structTy
        sprintf "%s = hw.struct_create (%s) : %s" (ssaToString result) valsStr tyStr
    | HWStructExtract (result, input, fieldName, structTy) ->
        let tyStr = hwTypeToString pointer structTy
        sprintf "%s = hw.struct_extract %s[\"%s\"] : %s" (ssaToString result) (ssaToString input) fieldName tyStr
    | HWStructInject (result, input, fieldName, newValue, structTy) ->
        let tyStr = hwTypeToString pointer structTy
        sprintf "%s = hw.struct_inject %s[\"%s\"], %s : %s" (ssaToString result) (ssaToString input) fieldName (ssaToString newValue) tyStr
    | HWInstance (result, instName, moduleName, inputs, outputs) ->
        // hw.instance "instName" @moduleName(portName: %ssa : type, ...) -> (outName: type, ...)
        let inputsStr = inputs |> List.map (fun (pn, ssa, ty) -> sprintf "%s: %s: %s" pn (ssaToString ssa) (hwTypeToString pointer ty)) |> String.concat ", "
        let outputsStr = outputs |> List.map (fun (pn, ty) -> sprintf "%s: %s" pn (hwTypeToString pointer ty)) |> String.concat ", "
        sprintf "%s = hw.instance \"%s\" @%s(%s) -> (%s)" (ssaToString result) instName moduleName inputsStr outputsStr
    | HWAggregateConstant (result, structTy) ->
        let rec zeroLiteral (ty: MLIRType) : string =
            match ty with
            | TStruct (fields, _) ->
                let inner = fields |> List.map (fun (_, ft) -> zeroLiteral ft) |> String.concat ", "
                sprintf "[%s]" inner
            | _ -> sprintf "0 : %s" (hwTypeToString pointer ty)
        sprintf "%s = hw.aggregate_constant [%s] : %s"
            (ssaToString result)
            (match structTy with
             | TStruct (fields, _) -> fields |> List.map (fun (_, ft) -> zeroLiteral ft) |> String.concat ", "
             | _ -> zeroLiteral structTy)
            (hwTypeToString pointer structTy)

/// Serialize SeqOp to CIRCT MLIR text (seq dialect)
let seqOpToString (pointer: Result<int, string>) (op: SeqOp) : string =
    match op with
    | SeqCompreg (result, input, clk, resetOpt, ty) ->
        match resetOpt with
        | Some (resetSignal, resetValue) ->
            sprintf "%s = seq.compreg %s, %s reset %s, %s : %s"
                (ssaToString result) (ssaToString input) (ssaToString clk)
                (ssaToString resetSignal) (ssaToString resetValue) (typeToString pointer ty)
        | None ->
            sprintf "%s = seq.compreg %s, %s : %s"
                (ssaToString result) (ssaToString input) (ssaToString clk) (typeToString pointer ty)

/// Serialize an SMT dialect type to MLIR text
let smtTypeToString (ty: SMTType) : string =
    match ty with
    | SMTBool -> "!smt.bool"
    | SMTInt -> "!smt.int"
    | SMTBV w -> sprintf "!smt.bv<%d>" w

/// Serialize SMTOp to MLIR text (verification modules)
let smtOpToString (pointer: Result<int, string>) (inner: MLIROp -> string) (op: SMTOp) : string =
    match op with
    | SMTSolver body ->
        let bodyStr = body |> List.map inner |> String.concat "\n    "
        sprintf "smt.solver () : () -> () {\n    %s\n  }" bodyStr
    | SMTSetLogic logic ->
        sprintf "smt.set_logic \"%s\"" logic
    | SMTDeclareFun (result, name, ty) ->
        sprintf "%s = smt.declare_fun \"%s\" : %s" (ssaToString result) name (smtTypeToString ty)
    | SMTIntConstant (result, value) ->
        sprintf "%s = smt.int.constant %d" (ssaToString result) value
    | SMTBigIntConstant (result, value) ->
        sprintf "%s = smt.int.constant %s" (ssaToString result) (value.ToString(System.Globalization.CultureInfo.InvariantCulture))
    | SMTBVConstant (result, value, width) ->
        sprintf "%s = smt.bv.constant #smt.bv<%d> : !smt.bv<%d>" (ssaToString result) value width
    | SMTIntAdd (result, lhs, rhs) ->
        sprintf "%s = smt.int.add %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs)
    | SMTIntSub (result, lhs, rhs) ->
        sprintf "%s = smt.int.sub %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs)
    | SMTIntMod (result, lhs, rhs) ->
        sprintf "%s = smt.int.mod %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs)
    | SMTIntDiv (result, lhs, rhs) ->
        sprintf "%s = smt.int.div %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs)
    | SMTIntMul (result, lhs, rhs) ->
        sprintf "%s = smt.int.mul %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs)
    | SMTIntCmp (result, pred, lhs, rhs) ->
        let predStr =
            match pred with
            | SmtLt -> "lt" | SmtLe -> "le" | SmtGt -> "gt" | SmtGe -> "ge"
        sprintf "%s = smt.int.cmp %s %s, %s" (ssaToString result) predStr (ssaToString lhs) (ssaToString rhs)
    | SMTEq (result, lhs, rhs, ty) ->
        sprintf "%s = smt.eq %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (smtTypeToString ty)
    | SMTAnd (result, operands) ->
        sprintf "%s = smt.and %s" (ssaToString result) (operands |> List.map ssaToString |> String.concat ", ")
    | SMTOr (result, operands) ->
        sprintf "%s = smt.or %s" (ssaToString result) (operands |> List.map ssaToString |> String.concat ", ")
    | SMTNot (result, operand) ->
        sprintf "%s = smt.not %s" (ssaToString result) (ssaToString operand)
    | SMTIte (result, condition, thenValue, elseValue, ty) ->
        sprintf "%s = smt.ite %s, %s, %s : %s" (ssaToString result) (ssaToString condition)
            (ssaToString thenValue) (ssaToString elseValue) (smtTypeToString ty)
    | SMTAssert operand ->
        sprintf "smt.assert %s" (ssaToString operand)
    | SMTCheck ->
        "smt.check sat {} unknown {} unsat {}"

/// Serialize MemRefOp to MLIR text
let memrefOpToString (pointer: Result<int, string>) (op: MemRefOp) : string =
    match op with
    | MemRefOp.LoadAligned (result, memref, indices, _, memrefType, alignment) ->
        let indicesStr = indices |> List.map ssaToString |> String.concat ", "
        sprintf "%s = memref.load %s[%s] {alignment = %d : i64} : %s"
            (ssaToString result) (ssaToString memref) indicesStr alignment (typeToString pointer memrefType)
    | MemRefOp.StoreAligned (value, memref, indices, _, memrefType, alignment) ->
        let indicesStr = indices |> List.map ssaToString |> String.concat ", "
        sprintf "memref.store %s, %s[%s] {alignment = %d : i64} : %s"
            (ssaToString value) (ssaToString memref) indicesStr alignment (typeToString pointer memrefType)
    | MemRefOp.Load (result, memref, indices, _elemType, memrefType) ->
        // Build indices string
        let indicesStr = if List.isEmpty indices then "" else sprintf "[%s]" (indices |> List.map ssaToString |> String.concat ", ")
        // Use the passed memrefType directly (no heuristic reconstruction)
        sprintf "%s = memref.load %s%s : %s"
            (ssaToString result) (ssaToString memref) indicesStr (typeToString pointer memrefType)
    | MemRefOp.Store (value, memref, indices, _elemType, memrefType) ->
        // Build indices string
        let indicesStr = if List.isEmpty indices then "" else sprintf "[%s]" (indices |> List.map ssaToString |> String.concat ", ")
        // Use the passed memrefType directly (no heuristic reconstruction)
        sprintf "memref.store %s, %s%s : %s"
            (ssaToString value) (ssaToString memref) indicesStr (typeToString pointer memrefType)
    | MemRefOp.Alloca (result, memrefType, alignmentOpt) ->
        match alignmentOpt with
        | Some alignment ->
            sprintf "%s = memref.alloca() {alignment = %d : i64} : %s"
                (ssaToString result) alignment (typeToString pointer memrefType)
        | None ->
            sprintf "%s = memref.alloca() : %s" (ssaToString result) (typeToString pointer memrefType)
    | MemRefOp.AllocaDynamic (result, count, elementType, alignment) ->
        sprintf "%s = memref.alloca(%s) {alignment = %d : i64} : %s"
            (ssaToString result) (ssaToString count) alignment (typeToString pointer (TMemRef elementType))
    | MemRefOp.Alloc (result, sizeSSA, elemType, alignmentOpt) ->
        // Heap allocation with runtime size: memref.alloc(%size) : memref<?xelemType>
        let memrefType = TMemRef elemType
        let alignment = alignmentOpt |> Option.map (sprintf " {alignment = %d : i64}") |> Option.defaultValue ""
        sprintf "%s = memref.alloc(%s)%s : %s"
            (ssaToString result) (ssaToString sizeSSA) alignment (typeToString pointer memrefType)
    | MemRefOp.Dealloc (memref, memrefType) ->
        sprintf "memref.dealloc %s : %s" (ssaToString memref) (typeToString pointer memrefType)
    | MemRefOp.AllocStatic (result, memrefType, alignmentOpt) ->
        // Heap allocation with compile-time size: memref.alloc() : memref<NxT>
        // Like Alloca but heap-allocated — survives function return
        match alignmentOpt with
        | Some alignment ->
            sprintf "%s = memref.alloc() {alignment = %d : i64} : %s"
                (ssaToString result) alignment (typeToString pointer memrefType)
        | None ->
            sprintf "%s = memref.alloc() : %s" (ssaToString result) (typeToString pointer memrefType)
    | MemRefOp.Copy (source, destination, sourceType, destinationType) ->
        sprintf "memref.copy %s, %s : %s to %s"
            (ssaToString source) (ssaToString destination)
            (typeToString pointer sourceType) (typeToString pointer destinationType)
    | MemRefOp.SubView (result, source, offsets, resultType) ->
        let offsetsStr = offsets |> List.map ssaToString |> String.concat ", "
        sprintf "%s = memref.subview %s[%s] : %s"
            (ssaToString result) (ssaToString source) offsetsStr (typeToString pointer resultType)
    | MemRefOp.SubViewSlice (result, source, offsets, sizes, strides, sourceType) ->
        // Proper MLIR memref.subview with 3 bracket groups: [offsets] [sizes] [strides]
        // Result has strided layout — callers must copy to contiguous buffer for FFI use.
        let fmtParam = function
            | SubViewParam.Static n -> string n
            | SubViewParam.Dynamic s -> ssaToString s
        let offsetsStr = offsets |> List.map ssaToString |> String.concat ", "
        let sizesStr = sizes |> List.map fmtParam |> String.concat ", "
        let stridesStr = strides |> List.map fmtParam |> String.concat ", "
        let elemType =
            match sourceType with
            | TMemRef t | TMemRefStatic (_, t) | TMemRefScalar t -> t
            | t -> failwithf "memref.subview: Alex emission did not supply a memref source for SSA %s: the source is typed %A" (ssaToString result) t
        let elemStr = typeToString pointer elemType
        let sizeStr =
            match sizes with
            | [SubViewParam.Static n] -> string n
            | _ -> "?"
        let strideStr =
            match strides with
            | [SubViewParam.Static n] -> string n
            | _ -> "?"
        let stridedTypeStr = sprintf "memref<%sx%s, strided<[%s], offset: ?>>" sizeStr elemStr strideStr
        sprintf "%s = memref.subview %s[%s] [%s] [%s] : %s to %s"
            (ssaToString result) (ssaToString source) offsetsStr sizesStr stridesStr
            (typeToString pointer sourceType) stridedTypeStr
    | MemRefOp.ExtractBasePtr (result, memref, ty) ->
        // Extract pointer as platform word (index type) - PORTABLE!
        // Returns index (platform word size), caller must cast to target type if needed
        sprintf "%s = memref.extract_aligned_pointer_as_index %s : %s -> index"
            (ssaToString result) (ssaToString memref) (typeToString pointer ty)
    | MemRefOp.ExtractStridedMetadata(baseBuffer, offset, size, stride, source, sourceType, elementType) ->
        sprintf "%s, %s, %s, %s = memref.extract_strided_metadata %s : %s -> %s, index, index, index"
            (ssaToString baseBuffer) (ssaToString offset) (ssaToString size) (ssaToString stride)
            (ssaToString source) (typeToString pointer sourceType) (typeToString pointer (TMemRefScalar elementType))
    | MemRefOp.GetGlobal (result, globalName, memrefType) ->
        // memref.get_global @symbol_name : memref<...>
        sprintf "%s = memref.get_global @%s : %s"
            (ssaToString result) globalName (typeToString pointer memrefType)
    | MemRefOp.Dim (result, memref, index, memrefType) ->
        // memref.dim %memref, %index : memref<...>
        sprintf "%s = memref.dim %s, %s : %s"
            (ssaToString result) (ssaToString memref) (ssaToString index) (typeToString pointer memrefType)
    | MemRefOp.Cast (result, source, srcType, destType) ->
        // memref.cast %source : srcType to destType
        sprintf "%s = memref.cast %s : %s to %s"
            (ssaToString result) (ssaToString source) (typeToString pointer srcType) (typeToString pointer destType)
    | MemRefOp.ReinterpretCast (result, source, byteOffset, size, srcType, destType) ->
        // One operation, one line. A view of another element type, or at a byte
        // offset, is MemRefOp.View with its offset value, composed by the Pattern.
        sprintf "%s = memref.reinterpret_cast %s to offset: [%d], sizes: [%d], strides: [1] : %s to %s"
            (ssaToString result) (ssaToString source) byteOffset size (typeToString pointer srcType) (typeToString pointer destType)
    | MemRefOp.ReinterpretCastDynamic (result, source, offset, sizeSSA, srcType, destType) ->
        // memref.reinterpret_cast with dynamic size: reconstruct memref from pointer + known length
        // Used for string/array capture extraction where size is loaded from closure struct
        sprintf "%s = memref.reinterpret_cast %s to offset: [%d], sizes: [%s], strides: [1] : %s to %s"
            (ssaToString result) (ssaToString source) offset (ssaToString sizeSSA) (typeToString pointer srcType) (typeToString pointer destType)
    | MemRefOp.View (result, source, offsetSSA, srcType, destType) ->
        // memref.view: typed view of byte buffer (different element type allowed)
        // Portable across all targets: CPU (→ GEP), FPGA (→ typed memory port), NPU (→ typed channel)
        sprintf "%s = memref.view %s[%s][] : %s to %s"
            (ssaToString result) (ssaToString source) (ssaToString offsetSSA) (typeToString pointer srcType) (typeToString pointer destType)

/// Shared portable container grammar. Child holes contain operations, never
/// backend text or a callback that could introduce target instructions.
type ContainerPart =
    | Text of string
    | Children of prefix: string * separator: string * operations: MLIROp list
    | NamedChildren of prefix: string * separator: string * arguments: string list * operations: MLIROp list

let private withArgumentNames arguments text =
    arguments |> List.indexed |> List.rev
    |> List.fold (fun (body: string) (index, name) -> body.Replace(sprintf "%%arg%d" index, sprintf "%%%s" name)) text

let containerFrame pointer = function
    | MLIROp.HWOp(HWModule(name, inputs, outputs, body)) ->
        let inputPorts = inputs |> List.map (fun (name, ty) -> sprintf "in %%%s: %s" name (hwTypeToString pointer ty))
        let outputPorts = outputs |> List.map (fun (name, ty) -> sprintf "out %s: %s" name (hwTypeToString pointer ty))
        Some [Text(sprintf "hw.module @%s(%s) {\n    " name (String.concat ", " (inputPorts @ outputPorts)))
              NamedChildren("", "\n    ", List.map fst inputs, body); Text "\n}"]
    | MLIROp.FuncOp(FuncDef(name, args, resultTypes, body, _))
    | MLIROp.NoUnwindFunction(FuncDef(name, args, resultTypes, body, _)) as operation ->
        let argsStr = args |> List.map (fun (ssa, ty) -> sprintf "%s: %s" (ssaToString ssa) (typeToString pointer ty)) |> String.concat ", "
        let attributes = match operation with NoUnwindFunction _ -> " attributes {passthrough = [\"nounwind\"]}" | _ -> ""
        Some [Text(sprintf "func.func @%s(%s) -> %s%s {\n    " (symbolName name) argsStr (resultTypesToString pointer resultTypes) attributes)
              Children("", "\n    ", body); Text "\n}"]
    | MLIROp.SCFOp(SCFOp.While(condition, body)) ->
        Some [Text "scf.while : () -> () {\n      "; Children("", "\n      ", condition)
              Text "\n    } do {\n      "; Children("", "\n      ", body); Text "\n    }"]
    | MLIROp.SCFOp(SCFOp.If(condition, yes, no, result)) ->
        let prefix, suffix =
            match result with
            | Some(ssa, ty) -> sprintf "%s = " (ssaToString ssa), sprintf " -> (%s)" (typeToString pointer ty)
            | None -> "", ""
        let first = [Text(sprintf "%sscf.if %s%s {\n      " prefix (ssaToString condition) suffix); Children("", "\n      ", yes)]
        Some(first @ (match no with
                      | Some body -> [Text "\n    } else {\n      "; Children("", "\n      ", body); Text "\n    }"]
                      | None -> [Text "\n    }"]))
    | MLIROp.SCFOp(SCFOp.For(induction, lower, upper, step, body)) ->
        Some [Text(sprintf "scf.for %s = %s to %s step %s {\n      " (ssaToString induction) (ssaToString lower) (ssaToString upper) (ssaToString step))
              Children("", "\n      ", body); Text "\n    }"]
    | MLIROp.SCFOp(SCFOp.IndexSwitch(selector, cases, fallback, results)) ->
        let prefix, resultTypes =
            match results with
            | [] -> "", ""
            | _ ->
                let names = results |> List.map (fst >> ssaToString) |> String.concat ", "
                let types = results |> List.map (snd >> typeToString pointer) |> String.concat ", "
                names + " = ", " -> " + types
        let regions = (cases |> List.map (fun (label, body) -> sprintf "case %d" label, body)) @ ["default", fallback]
        let parts = regions |> List.mapi (fun index (label, body) ->
            [Text((if index = 0 then "" else "\n    ") + label + " {\n      "); Children("", "\n      ", body); Text "\n    }"]) |> List.concat
        Some(Text(sprintf "%sscf.index_switch %s%s\n    " prefix (ssaToString selector) resultTypes) :: parts)
    | _ -> None

let moduleFrame moduleName operations =
    match moduleName with
    | Some name -> [Text(sprintf "module @%s {\n" name); Children("  ", "\n", operations); Text "\n}"]
    | None -> [Text "module {\n"; Children("  ", "\n", operations); Text "\n}"]

/// Serialize top-level MLIROp to portable MLIR text.
let rec opToString (pointer: Result<int, string>) (op: MLIROp) : string =
    match containerFrame pointer op with
    | Some parts ->
        parts |> List.map (function
            | Text text -> text
            | Children(prefix, separator, operations) -> operations |> List.map (fun child -> prefix + opToString pointer child) |> String.concat separator
            | NamedChildren(prefix, separator, arguments, operations) ->
                operations |> List.map (fun child -> prefix + opToString pointer child) |> String.concat separator |> withArgumentNames arguments)
        |> String.concat ""
    | None -> leafToString pointer op

and private leafToString (pointer: Result<int, string>) (op: MLIROp) : string =
    match op with
    | MLIROp.MmioLoad _ | MLIROp.MmioStore _ ->
        raise (TargetRealizationRequired "Portable MMIO intent requires realization by the selected backend.")
    | MLIROp.ArithOp aop -> arithOpToString pointer aop
    | MLIROp.MemRefOp mop -> memrefOpToString pointer mop
    | MLIROp.NoUnwindFunction _ -> failwith "NoUnwindFunction requires a function definition"
    | MLIROp.FuncOp fop ->
        match fop with
        | FuncDef _ -> failwith "Function definition requires its portable container frame"
        | FuncDecl (name, paramTypes, resultTypes, _visibility, byvalParams) ->
            if not byvalParams.IsEmpty then
                failwithf "Foreign declaration '%s' requires a source-settled aggregate ABI realization; portable func declarations cannot realize byval metadata" name
            let paramsStr = paramTypes |> List.map (typeToString pointer) |> String.concat ", "
            sprintf "func.func private @%s(%s) -> %s" (symbolName name) paramsStr (resultTypesToString pointer resultTypes)
        | BoundaryFuncDecl (declaration, parameters, results) ->
            if declaration.Parameters |> List.exists (fun (_, scalar) ->
                match scalar with Fidelity.PSG.BoundaryScalar.WritableBytes _ -> true | _ -> false) then
                raise (TargetRealizationRequired "Writable byte declarations require the selected backend and their exact source accounts.")
            let paramsStr = parameters |> List.map (typeToString pointer) |> String.concat ", "
            sprintf "func.func private @%s(%s) -> %s" (symbolName declaration.Symbol) paramsStr
                (resultTypesToString pointer results)
        | IntrinsicWriteDecl declaration ->
            let paramsStr = IntrinsicWriteAbi.parameters declaration |> List.map (typeToString pointer) |> String.concat ", "
            sprintf "func.func private @%s(%s) -> %s" (symbolName declaration.Symbol) paramsStr
                (resultTypesToString pointer (IntrinsicWriteAbi.results declaration))
        | FuncCall (results, funcName, args) ->
            let argSSAs = args |> List.map (fun v -> ssaToString v.SSA) |> String.concat ", "
            let argTypes = args |> List.map (fun v -> typeToString pointer v.Type) |> String.concat ", "
            sprintf "%sfunc.call @%s(%s) : (%s) -> %s" (resultAssignment results) (symbolName funcName) argSSAs argTypes
                (resultTypesToString pointer (List.map _.Type results))
        | FuncCallIndirect (results, callee, args) ->
            let argSSAs = args |> List.map (fun v -> ssaToString v.SSA) |> String.concat ", "
            let argTypes = args |> List.map (fun v -> typeToString pointer v.Type) |> String.concat ", "
            sprintf "%sfunc.call_indirect %s(%s) : (%s) -> %s" (resultAssignment results) (ssaToString callee) argSSAs argTypes
                (resultTypesToString pointer (List.map _.Type results))
        | FuncConstant (result, funcName, funcTy) ->
            sprintf "%s = func.constant @%s : %s" (ssaToString result) (symbolName funcName) (typeToString pointer funcTy)
        | Return values ->
            match values with
            | [] -> "func.return"
            | _ ->
                if values |> List.exists (fun value -> value.Type = TVoid) then
                    failwith "Function return cannot contain a TVoid value"
                let operands = values |> List.map (fun value -> ssaToString value.SSA) |> String.concat ", "
                let types = values |> List.map (fun value -> typeToString pointer value.Type) |> String.concat ", "
                sprintf "func.return %s : %s" operands types
    | MLIROp.GlobalString (name, content, storageLength, obligations) ->
        // Emit memref.global (portable MLIR) with null sentinel byte for C interop.
        // Clef strings are (ptr, length) — the sentinel is a storage detail invisible
        // to the type system, ensuring .Pointer yields C-compatible null-terminated data.
        let bytes = System.Text.Encoding.UTF8.GetBytes(content)
        let bytesWithSentinel = Array.append bytes [| 0uy |]
        let denseStr = bytesWithSentinel |> Array.map (sprintf "%d") |> String.concat ", "
        // The obligations constraining this storage, reified on the op as a
        // discardable attribute (PHG paper 2.4b). The artifact carries the
        // correspondence explicitly; the artifact-side check reads it here
        // rather than reconstructing it by matching content.
        let attrs =
            match obligations with
            | [] -> ""
            | names -> sprintf " {clef.obligations = [%s]}" (names |> List.map (sprintf "\"%s\"") |> String.concat ", ")
        sprintf "memref.global \"private\" constant @%s : memref<%dxi8> = dense<[%s]>%s" name storageLength denseStr attrs
    | MLIROp.GlobalBytePool (name, bytes, alignment, obligations) ->
        let dense = bytes |> List.map string |> String.concat ", "
        let anchors =
            match obligations with
            | [] -> ""
            | names -> sprintf ", clef.obligations = [%s]" (names |> List.map (sprintf "\"%s\"") |> String.concat ", ")
        sprintf "memref.global \"private\" constant @%s : memref<%dxi8> = dense<[%s]> {alignment = %d : i64%s}"
            name bytes.Length dense alignment anchors
    | MLIROp.GlobalMemref (name, memrefType, authority) ->
        // Zero-initialized static storage for a program-lifetime value (the program-lifetime
        // point of the lifetime lattice). Not `constant`: the closure struct is written into
        // this storage at construction. `uninitialized` is correct because every read is
        // preceded by the construction store; a heap-free target places this in .bss/Sram.
        let alignment =
            match authority with
            | Some entry -> sprintf " {alignment = %d : i64}" entry.Alignment
            | None ->
                failwithf "PSG settlement (program storage) did not settle a storage entry for the writable global @%s: an unowned global has no alignment to write" name
        sprintf "memref.global \"private\" @%s : %s = uninitialized%s" name (typeToString pointer memrefType) alignment
    | MLIROp.NativeEntrySlotDecl(_globalName, storage, entry, functionType) ->
        match storage.Shape, functionType with
        | Fidelity.PSG.ProgramStorageShape.NativeEntry formation, TFunc _ when formation = entry -> ()
        | _ -> invalidOp "Native entry placeholder declaration differs from its typed source storage formation."

        let storeName, loadName = NativeEntrySlotSymbols.names storage.Identity
        let slotType = TMemRefStatic(storage.Bytes, TInt(IntWidth 8))
        let slotText = typeToString pointer slotType
        let functionText = typeToString pointer functionType

        sprintf
            "func.func private @%s(%s, %s)\nfunc.func private @%s(%s) -> (%s)"
            storeName
            slotText
            functionText
            loadName
            slotText
            functionText
    | MLIROp.NativeEntrySlotStore(identity, _entry, destination, value) ->
        match destination.Type, value.Type with
        | TMemRefStatic(_, TInt(IntWidth 8)), TFunc _ -> ()
        | _ -> invalidOp "Native entry placeholder store requires its byte container and typed function value."

        let storeName, _ = NativeEntrySlotSymbols.names identity

        sprintf
            "func.call @%s(%s, %s) : (%s, %s) -> ()"
            storeName
            (ssaToString destination.SSA)
            (ssaToString value.SSA)
            (typeToString pointer destination.Type)
            (typeToString pointer value.Type)
    | MLIROp.NativeEntrySlotLoad(identity, _entry, source, result) ->
        match source.Type, result.Type with
        | TMemRefStatic(_, TInt(IntWidth 8)), TFunc _ -> ()
        | _ -> invalidOp "Native entry placeholder load requires its byte container and typed function result."

        let _, loadName = NativeEntrySlotSymbols.names identity

        sprintf
            "%s = func.call @%s(%s) : (%s) -> (%s)"
            (ssaToString result.SSA)
            loadName
            (ssaToString source.SSA)
            (typeToString pointer source.Type)
            (typeToString pointer result.Type)
    | MLIROp.GlobalArray(name, memrefType, authority) ->
        let values =
            authority.Initializers |> Option.defaultWith (fun () -> invalidOp "Immutable array lacks its source-published initializer.")
            |> List.map (function
                | Fidelity.PSG.NativeLiteral.Int(value, _) -> string value
                | Fidelity.PSG.NativeLiteral.UInt(value, _) -> string value
                | Fidelity.PSG.NativeLiteral.Bool value -> if value then "true" else "false"
                | Fidelity.PSG.NativeLiteral.Char value -> string (int value)
                | Fidelity.PSG.NativeLiteral.Float(value, _) when System.Double.IsFinite value ->
                    let text = value.ToString("R", System.Globalization.CultureInfo.InvariantCulture)
                    if text.Contains('.') || text.Contains('E') || text.Contains('e') then text else text + ".0"
                | other -> invalidOp (sprintf "Unsupported published array initializer: %A" other))
        sprintf "memref.global \"private\" constant @%s : %s = dense<[%s]> {alignment = %d : i64}"
            name (typeToString pointer memrefType) (String.concat ", " values) authority.Alignment
    | MLIROp.IndexOp iop ->
        match iop with
        | IndexOp.IndexConst (result, value) ->
            sprintf "%s = arith.constant %d : index" (ssaToString result) value
        | IndexOp.IndexBoolConst (result, value) ->
            let boolVal = if value then 1 else 0
            sprintf "%s = arith.constant %d : i1" (ssaToString result) boolVal
        | IndexOp.IndexCastS (result, operand, srcTy, destTy) ->
            sprintf "%s = index.casts %s : %s to %s" (ssaToString result) (ssaToString operand) (typeToString pointer srcTy) (typeToString pointer destTy)
        | IndexOp.IndexCastU (result, operand, srcTy, destTy) ->
            sprintf "%s = index.castu %s : %s to %s" (ssaToString result) (ssaToString operand) (typeToString pointer srcTy) (typeToString pointer destTy)
        | IndexOp.IndexCmp (result, pred, lhs, rhs) ->
            let predStr =
                match pred with
                | Eq -> "eq" | Ne -> "ne"
                | Slt -> "slt" | Sle -> "sle"
                | Sgt -> "sgt" | Sge -> "sge"
                | Ult -> "ult" | Ule -> "ule"
                | Ugt -> "ugt" | Uge -> "uge"
            sprintf "%s = index.cmp %s(%s, %s)" (ssaToString result) predStr (ssaToString lhs) (ssaToString rhs)
        | IndexOp.IndexAdd (result, lhs, rhs) ->
            sprintf "%s = index.add %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs)
        | IndexOp.IndexMul (result, lhs, rhs) ->
            sprintf "%s = index.mul %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs)
        | _ ->
            failwithf "backend (MLIR text) has no serialization for the index operation %A; it was emitted without one and is never written as a comment" iop
    | MLIROp.Assert (condition, message) ->
        sprintf "cf.assert %s, \"%s\"" (ssaToString condition) (stringAttributeValue message)
    | MLIROp.SCFOp scfOp ->
        match scfOp with
        | SCFOp.While _ | SCFOp.If _ | SCFOp.For _ | SCFOp.IndexSwitch _ ->
            failwith "Structured control flow requires its portable container frame"
        | SCFOp.Yield vals ->
            match vals with
            | [] -> "scf.yield"
            | _ ->
                let values = vals |> List.map (fst >> ssaToString) |> String.concat ", "
                let types = vals |> List.map (snd >> typeToString pointer) |> String.concat ", "
                sprintf "scf.yield %s : %s" values types
        | SCFOp.Condition (cond, args) ->
            let argsStr = args |> List.map ssaToString |> String.concat ", "
            sprintf "scf.condition(%s) %s" (ssaToString cond) argsStr
    | MLIROp.CombOp cop -> combOpToString pointer cop
    | MLIROp.HWOp hop -> hwOpToString pointer hop
    | MLIROp.SeqOp sop -> seqOpToString pointer sop
    | MLIROp.SMTOp sop -> smtOpToString pointer (opToString pointer) sop
    | MLIROp.SpatialModule declaration ->
        let name,site,kind =
            match declaration with
            | Fidelity.PSG.SpatialModuleWitness.Hardware plan -> plan.Name,plan.Site,"hardware"
            | Fidelity.PSG.SpatialModuleWitness.Kernel plan -> plan.Name,plan.Site,"kernel"
        let (Fidelity.PSG.NodeId sourceId) = site
        sprintf "module @%s attributes {clef.spatial_source = \"%d\", clef.spatial_kind = \"%s\"} {}"
            (symbolName name) sourceId kind
    | MLIROp.WritableBufferCall _ ->
        raise (TargetRealizationRequired "Writable byte calls require the selected backend and their exact source accounts.")
    | MLIROp.Utf8Validate _ | MLIROp.Utf8SnapshotRetire _ ->
        raise (TargetRealizationRequired "Checked text requires the selected backend and its exact snapshot, validator and retirement accounts.")
    | MLIROp.OptionalEntryCall _ ->
        raise (TargetRealizationRequired "Optional entry calls require the selected backend and their exact source conversion accounts.")
    | MLIROp.ResourceImport _ | MLIROp.ResourceCall _
    | MLIROp.ResourceOptionTag _ | MLIROp.ResourceOptionPayload _ | MLIROp.ResourceAlias _ ->
        raise (TargetRealizationRequired "Resource operations require the selected backend and their exact source accounts.")
    | MLIROp.RawMLIR text -> portableText text
    | _ ->
        // Block and Region have no text form here: reaching one is a stop, never a comment.
        failwithf "backend (MLIR text) has no serialization for the operation %A; it was emitted without one and is never written as a comment" op

/// Serialize a list of operations with proper indentation
/// Serialize one op; a width failure inside it is re-raised naming the op, so that the
/// stop says which value had no width rather than only that one did.
let private opToStringNamed (pointer: Result<int, string>) (op: MLIROp) : string =
    try opToString pointer op |> portableText
    with ex when ex.Message.StartsWith "Width inference failure" ->
        let rendered = sprintf "%A" op
        let shown = if rendered.Length > 400 then rendered.Substring(0, 400) + " ..." else rendered
        failwith (ex.Message + "\nWhile serialising: " + shown)

let opsToString (pointer: Result<int, string>) (ops: MLIROp list) (indent: string) : string =
    ops
    |> List.map (opToStringNamed pointer)
    |> List.map (fun line -> indent + line)
    |> String.concat "\n"

/// Serialize a complete MLIR module
let private moduleToStringOption (pointer: Result<int, string>) (moduleName: string option) (ops: MLIROp list) : string =
    moduleFrame moduleName ops
    |> List.map (function
        | Text text -> text
        | Children(prefix, separator, operations) -> operations |> List.map (fun child -> prefix + opToStringNamed pointer child) |> String.concat separator
        | NamedChildren(prefix, separator, arguments, operations) ->
            operations |> List.map (fun child -> prefix + opToStringNamed pointer child) |> String.concat separator |> withArgumentNames arguments)
    |> String.concat ""
    |> portableText

let moduleToString pointer moduleName operations = moduleToStringOption pointer (Some moduleName) operations

/// Validate every portable operation before reporting target deferral. A target
/// operation cannot hide a later serialization or source-width refusal.
let moduleText (pointer: Result<int, string>) (moduleName: string option) (ops: MLIROp list) : ModuleText =
    let validateFrame parts =
        parts |> List.iter (function
            | Text text -> portableText text |> ignore
            | Children(prefix, separator, _) | NamedChildren(prefix, separator, _, _) ->
                portableText prefix |> ignore; portableText separator |> ignore)
    moduleFrame moduleName ops |> validateFrame
    let needsTarget =
        OperationStructure.flatten ops
        |> List.map (fun operation ->
            match containerFrame pointer operation with
            | Some parts -> validateFrame parts; false
            | None ->
                try
                    opToStringNamed pointer operation |> ignore
                    false
                with TargetRealizationRequired _ -> true)
        |> List.contains true
    if needsTarget then NeedsTargetRealization
    else moduleToStringOption pointer moduleName ops |> Available
