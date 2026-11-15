/// MLIR Serialization
///
/// Converts structured MLIR types and operations to MLIR text format.
/// This is the ONLY place where sprintf is used for MLIR text generation.
/// All upstream code (witnesses, patterns, elements) works with structured MLIROp.
module Alex.Dialects.Core.Serialize

open Alex.Dialects.Core.Types

/// Text escapes remain portable. Quoted data, symbols and comments are not
/// dialect operations; a quoted generic operation is identified by its operands.
let private portableText (text: string) : Result<string, string> =
    let refuse () = Error "ALEX004: LLVM dialect constructs belong to backend realization, never Alex portable output."
    let length = String.length text
    let at position token =
        position + String.length token <= length
        && (token |> String.mapi (fun offset c -> if text[position + offset] = c then '1' else '0') |> String.forall ((=) '1'))
    let identifier c = Alex.Text.isAsciiLetter c || Alex.Text.isAsciiDigit c || c = '_' || c = '.' || c = '$'
    let rec skip predicate position =
        if position < length && predicate text[position] then skip predicate (position + 1) else position
    let hex c =
        if '0' <= c && c <= '9' then Some(int c - int '0')
        elif 'a' <= c && c <= 'f' then Some(int c - int 'a' + 10)
        elif 'A' <= c && c <= 'F' then Some(int c - int 'A' + 10)
        else None
    let rec quoted position reversed =
        if position >= length then Error "Unterminated quoted MLIR token."
        else
            match text[position] with
            | '"' -> Ok (position + 1, reversed |> List.rev |> String.concat "")
            | '\\' when position + 1 < length ->
                match hex text[position + 1], (if position + 2 < length then hex text[position + 2] else None) with
                | Some high, Some low -> quoted (position + 3) (string (char (high * 16 + low)) :: reversed)
                | _ -> quoted (position + 2) (string text[position + 1] :: reversed)
            | c -> quoted (position + 1) (string c :: reversed)
    let backendOperation token =
        Alex.Text.startsWith "llvm." token
        && String.length token > 5
        && (Alex.Text.isAsciiLetter token[5] || token[5] = '_')
    let rec scan position quotedOperation =
        if position < length then
            if at position "//" then scan (skip (fun c -> c <> '\r' && c <> '\n') (position + 2)) quotedOperation
            elif Alex.Text.isWhitespace text[position] then scan (position + 1) quotedOperation
            elif at position "!llvm." || at position "!llvm<" then refuse ()
            elif text[position] = '@' then
                if position + 1 < length && text[position + 1] = '"' then
                    match quoted (position + 2) [] with
                    | Ok (finish, _) -> scan finish false
                    | Error err -> Error err
                else
                    let finish = skip identifier (position + 1)
                    scan finish false
            elif text[position] = '"' then
                match quoted (position + 1) [] with
                | Ok (finish, token) -> scan finish (backendOperation token)
                | Error err -> Error err
            elif identifier text[position] then
                let finish = skip identifier position
                let token = String.init (finish - position) (fun offset -> string text[position + offset])
                if backendOperation token then refuse ()
                else scan finish false
            else
                if quotedOperation && text[position] = '(' then refuse ()
                else scan (position + 1) false
        else
            Ok text
    scan 0 false

type private SerializationStep<'T> =
    | Serialized of 'T
    | RequiresTarget of string
    | Refused of string

let private stepBind (f: 'T -> SerializationStep<'U>) (step: SerializationStep<'T>) : SerializationStep<'U> =
    match step with
    | Serialized v -> f v
    | RequiresTarget msg -> RequiresTarget msg
    | Refused msg -> Refused msg

let private stepMap (f: 'T -> 'U) (step: SerializationStep<'T>) : SerializationStep<'U> =
    match step with
    | Serialized v -> Serialized (f v)
    | RequiresTarget msg -> RequiresTarget msg
    | Refused msg -> Refused msg

let private stepPair (a: SerializationStep<'A>) (b: SerializationStep<'B>) : SerializationStep<'A * 'B> =
    match a, b with
    | Refused err, _ | _, Refused err -> Refused err
    | RequiresTarget msg, _ | _, RequiresTarget msg -> RequiresTarget msg
    | Serialized va, Serialized vb -> Serialized (va, vb)

let private stepFromResult (res: Result<'T, string>) : SerializationStep<'T> =
    match res with
    | Ok v -> Serialized v
    | Error msg -> Refused msg

let private stepToResult (step: SerializationStep<'T>) : Result<'T, string> =
    match step with
    | Serialized v -> Ok v
    | RequiresTarget msg
    | Refused msg -> Error msg

let private stepMapList (f: 'T -> SerializationStep<'U>) (items: 'T list) : SerializationStep<'U list> =
    let rec loop acc targetDeferral remaining =
        match remaining with
        | [] ->
            match targetDeferral with
            | Some msg -> RequiresTarget msg
            | None -> Serialized (List.rev acc)
        | item :: rest ->
            match f item with
            | Serialized v -> loop (v :: acc) targetDeferral rest
            | RequiresTarget msg ->
                let firstTarget = match targetDeferral with Some _ -> targetDeferral | None -> Some msg
                loop acc firstTarget rest
            | Refused msg -> Refused msg
    loop [] None items

/// MLIR symbol names are bare identifiers ([A-Za-z_][A-Za-z0-9_$.]*). A Clef function name may
/// carry an apostrophe (`process'`), which is legal in F# and in the linked ELF symbol but not
/// in a bare MLIR id; it is spelled `$` in the symbol (a character no Clef name contains).
let symbolName (name: string) : string =
    name |> String.map (fun c -> if c = '\'' then '$' elif (Alex.Text.isAsciiLetter c || Alex.Text.isAsciiDigit c) || c = '_' || c = '.' || c = '$' then c else '_')

/// MLIR string attributes carry bytes. Escape non-printable and non-ASCII UTF8
/// bytes as two hexadecimal digits, preserving embedded NUL and line breaks.
let private stringAttributeValue (value: string) : Result<string, string> =
    let rec validate position =
        if position < String.length value then
            let c = int value[position]
            if 0xD800 <= c && c <= 0xDBFF then
                if position + 1 >= String.length value || int value[position + 1] < 0xDC00 || int value[position + 1] > 0xDFFF then
                    Error "String attribute contains an unpaired UTF-16 surrogate."
                else
                    validate (position + 2)
            elif 0xDC00 <= c && c <= 0xDFFF then
                Error "String attribute contains an unpaired UTF-16 surrogate."
            else validate (position + 1)
        else
            Ok ()
    match validate 0 with
    | Error err -> Error err
    | Ok () ->
        BAREWire.Encoding.Text.toUtf8 value
        |> Array.map (fun b ->
            if b >= 32uy && b <= 126uy && b <> 34uy && b <> 92uy then string (char b)
            else sprintf "\\%02X" b)
        |> String.concat ""
        |> Ok


// ═══════════════════════════════════════════════════════════════════════════
// TYPE SERIALIZATION
// ═══════════════════════════════════════════════════════════════════════════

/// Spell an exact positive source-published integer width.
let intWidthToString (IntWidth bits) : Result<string, string> =
    if bits <= 0 then
        Error "An unresolved or nonpositive integer width reached serialization; a complete source-published representation is required."
    else
        Ok (sprintf "i%d" bits)

/// Convert FloatWidth to MLIR type string
let floatWidthToString (width: FloatWidth) : string =
    match width with
    | F32 -> "f32"
    | F64 -> "f64"

/// Convert MLIRType to MLIR text format string
let rec private typeToStringStep (pointer: Result<int, string>) (ty: MLIRType) : SerializationStep<string> =
    match ty with
    | TOpaqueHandle _ | TResourceOption _ ->
        RequiresTarget "Opaque resource carriers require the selected backend and their exact source accounts."
    | TInt width -> intWidthToString width |> stepFromResult
    | TFloat width -> Serialized (floatWidthToString width)
    | TFunc (paramTypes, resultTypes) ->
        stepPair (stepMapList (typeToStringStep pointer) paramTypes) (resultTypesToStringStep pointer resultTypes)
        |> stepMap (fun (paramStrs, resStr) -> sprintf "(%s) -> %s" (String.concat ", " paramStrs) resStr)
    | TMemRef elemTy ->
        typeToStringStep pointer elemTy |> stepMap (sprintf "memref<?x%s>")
    | TMemRefStatic (size, elemTy) ->
        typeToStringStep pointer elemTy |> stepMap (sprintf "memref<%dx%s>" size)
    | TMemRefScalar elemTy ->
        typeToStringStep pointer elemTy |> stepMap (sprintf "memref<%s>")
    | TVector (count, elemTy) ->
        typeToStringStep pointer elemTy |> stepMap (sprintf "vector<%dx%s>" count)
    | TIndex -> Serialized "index"
    | TVoid -> Serialized "()"  // Empty MLIR result list at a foreign function boundary
    | TStruct (_, Some bytes) ->
        // TStruct serializes as !hw.struct for CIRCT (FPGA) or memref for CPU.
        // This default path is CPU; hwTypeToString pointer handles the FPGA case.
        // The byte size is the settled layout's, read from the graph (the one size model).
        Serialized (sprintf "memref<%dxi8>" bytes.Size)
    | TStruct (fields, None) ->
        Refused (sprintf "typeToString: the struct {%s} reached serialization on a core with no settled layout" (fields |> List.map fst |> String.concat ", "))
    | TSeqClock -> Serialized "!seq.clock"
    | TTag caseCount ->
        // Default serialization: smallest power-of-2 integer that fits the case count
        // Platform-specific serializers (hw dialect) may override with exact bit widths
        if caseCount <= 2 then Serialized "i1"
        elif caseCount <= 256 then Serialized "i8"
        elif caseCount <= 65536 then Serialized "i16"
        else Serialized "i32"

/// Function results are a list. A sole function-typed result still needs the
/// enclosing result-list parentheses so its own arrow is unambiguous.
and private resultTypesToStringStep (pointer: Result<int, string>) (results: MLIRType list) : SerializationStep<string> =
    if List.contains TVoid results then
        Refused "Function result lists use [] for no result; TVoid is not a value type"
    else
        match results with
        | [result] when (match result with TFunc _ -> false | _ -> true) -> typeToStringStep pointer result
        | _ -> stepMapList (typeToStringStep pointer) results |> stepMap (fun strs -> strs |> String.concat ", " |> sprintf "(%s)")

/// FPGA-aware type serialization: TStruct → !hw.struct<...>, all others → typeToString pointer
/// Used by comb.* and other CIRCT ops that carry struct types on FPGA.
let rec private hwTypeToStringStep (pointer: Result<int, string>) (ty: MLIRType) : SerializationStep<string> =
    match ty with
    | TStruct (fields, _) ->
        fields
        |> stepMapList (fun (n, t) -> hwTypeToStringStep pointer t |> stepMap (sprintf "%s: %s" n))
        |> stepMap (fun fs -> sprintf "!hw.struct<%s>" (String.concat ", " fs))
    | _ -> typeToStringStep pointer ty

let typeToString (pointer: Result<int, string>) (ty: MLIRType) : Result<string, string> =
    typeToStringStep pointer ty |> stepToResult

let resultTypesToString (pointer: Result<int, string>) (results: MLIRType list) : Result<string, string> =
    resultTypesToStringStep pointer results |> stepToResult

let hwTypeToString (pointer: Result<int, string>) (ty: MLIRType) : Result<string, string> =
    hwTypeToStringStep pointer ty |> stepToResult

let private nodeIdValue (Fidelity.PSG.NodeId id) = id

let private describeTypeParamKind = function
    | Fidelity.PSG.TypeParamKind.Type -> "type"
    | Fidelity.PSG.TypeParamKind.Measure -> "measure"
    | Fidelity.PSG.TypeParamKind.Carrier -> "carrier"

let private describeConstructor (ctor: Fidelity.PSG.ConstructorIdentity) : string =
    String.concat "." (ctor.Declaration.Module @ [ctor.Declaration.Name])

let rec describeTypeIdentity (ty: Fidelity.PSG.TypeIdentity) : string =
    match ty with
    | Fidelity.PSG.TypeIdentity.Application(ctor, []) -> describeConstructor ctor
    | Fidelity.PSG.TypeIdentity.Application(ctor, args) ->
        sprintf "%s<%s>" (describeConstructor ctor) (args |> List.map describeTypeIdentity |> String.concat ", ")
    | Fidelity.PSG.TypeIdentity.Union(ctor, []) -> describeConstructor ctor
    | Fidelity.PSG.TypeIdentity.Union(ctor, cases) ->
        let caseNames = cases |> List.map (fun (name, _, _) -> name) |> String.concat " | "
        sprintf "%s(%s)" (describeConstructor ctor) caseNames
    | Fidelity.PSG.TypeIdentity.Numeric(carrier, _) ->
        match carrier with
        | Fidelity.PSG.CarrierIdentity.Constructor ctor -> describeConstructor ctor
        | Fidelity.PSG.CarrierIdentity.Variable(idx, kind) -> sprintf "'%s%d" (describeTypeParamKind kind) idx
    | Fidelity.PSG.TypeIdentity.Measure _ -> "measure"
    | Fidelity.PSG.TypeIdentity.Variable(idx, kind) -> sprintf "'%s%d" (describeTypeParamKind kind) idx
    | Fidelity.PSG.TypeIdentity.Function(domain, range) ->
        sprintf "(%s -> %s)" (describeTypeIdentity domain) (describeTypeIdentity range)
    | Fidelity.PSG.TypeIdentity.Tuple(isStruct, items) ->
        let joined = items |> List.map describeTypeIdentity |> String.concat " * "
        if isStruct then sprintf "struct(%s)" joined else sprintf "(%s)" joined
    | Fidelity.PSG.TypeIdentity.AnonymousRecord(isStruct, fields) ->
        let joined = fields |> List.map (fun (n, t) -> sprintf "%s: %s" n (describeTypeIdentity t)) |> String.concat "; "
        if isStruct then sprintf "struct{| %s |}" joined else sprintf "{| %s |}" joined
    | Fidelity.PSG.TypeIdentity.Forall(pars, body) ->
        let pStr = pars |> List.map (fun (i, k) -> sprintf "'%s%d" (describeTypeParamKind k) i) |> String.concat " "
        sprintf "forall %s. %s" pStr (describeTypeIdentity body)
    | Fidelity.PSG.TypeIdentity.Byref(kind, inner) ->
        let k =
            match kind with
            | Fidelity.PSG.ByrefKind.In -> "inref"
            | Fidelity.PSG.ByrefKind.Out -> "outref"
            | Fidelity.PSG.ByrefKind.InOut -> "byref"
        sprintf "%s<%s>" k (describeTypeIdentity inner)
    | Fidelity.PSG.TypeIdentity.NativePointer inner -> sprintf "nativeptr<%s>" (describeTypeIdentity inner)
    | Fidelity.PSG.TypeIdentity.Lazy inner -> sprintf "Lazy<%s>" (describeTypeIdentity inner)
    | Fidelity.PSG.TypeIdentity.Sequence inner -> sprintf "seq<%s>" (describeTypeIdentity inner)
    | Fidelity.PSG.TypeIdentity.Enumerator inner -> sprintf "enumerator<%s>" (describeTypeIdentity inner)
    | Fidelity.PSG.TypeIdentity.List inner -> sprintf "list<%s>" (describeTypeIdentity inner)
    | Fidelity.PSG.TypeIdentity.Map(k, v) -> sprintf "Map<%s, %s>" (describeTypeIdentity k) (describeTypeIdentity v)
    | Fidelity.PSG.TypeIdentity.Set inner -> sprintf "Set<%s>" (describeTypeIdentity inner)
    | Fidelity.PSG.TypeIdentity.Error msg -> sprintf "error<%s>" msg

let describeSettledSlot = function
    | Fidelity.PSG.SettledSlot.InlineBytes(bytes, align) -> sprintf "bytes(%d, align=%d)" bytes align
    | Fidelity.PSG.SettledSlot.Integer(bits, _) -> if bits > 0 then sprintf "i%d" bits else sprintf "i<unresolved:%d>" bits
    | Fidelity.PSG.SettledSlot.Bool -> "bool"
    | Fidelity.PSG.SettledSlot.Char -> "char"
    | Fidelity.PSG.SettledSlot.Real bits -> sprintf "f%d" bits
    | Fidelity.PSG.SettledSlot.Pointer words -> sprintf "ptr(%d words)" words
    | Fidelity.PSG.SettledSlot.Unit -> "unit"
    | Fidelity.PSG.SettledSlot.Opaque what -> sprintf "opaque(%s)" what
    | Fidelity.PSG.SettledSlot.CHandle(ht, bits, align) -> sprintf "chandle<%s, %d-bit, align=%d>" (describeTypeIdentity ht) bits align

let describeSettledLayout = function
    | Fidelity.PSG.SettledLayout.Record(fields, size, align) ->
        let fs = fields |> List.map (fun f -> sprintf "%s: %s" f.Name (describeSettledSlot f.Slot)) |> String.concat "; "
        sprintf "Record([%s], size=%s, align=%s)" fs (size |> Option.map string |> Option.defaultValue "none") (align |> Option.map string |> Option.defaultValue "none")
    | Fidelity.PSG.SettledLayout.Union(cases, payloadOffset, size, align) ->
        let cs =
            cases
            |> List.map (fun (name, slotOpt) ->
                match slotOpt with
                | Some slot -> sprintf "%s(%s)" name (describeSettledSlot slot)
                | None -> name)
            |> String.concat " | "
        sprintf "Union([%s], offset=%s, size=%s, align=%s)"
            cs
            (payloadOffset |> Option.map string |> Option.defaultValue "none")
            (size |> Option.map string |> Option.defaultValue "none")
            (align |> Option.map string |> Option.defaultValue "none")

let describeProgramStorageIdentity = function
    | Fidelity.PSG.ProgramStorageIdentity.Allocation id -> sprintf "Allocation (NodeId %d)" (nodeIdValue id)
    | Fidelity.PSG.ProgramStorageIdentity.BindingSlot id -> sprintf "BindingSlot (NodeId %d)" (nodeIdValue id)

let describeIntrinsicModule = function
    | Fidelity.PSG.IntrinsicModule.Sys -> "Sys"
    | Fidelity.PSG.IntrinsicModule.NativeDefault -> "NativeDefault"
    | Fidelity.PSG.IntrinsicModule.String -> "String"
    | Fidelity.PSG.IntrinsicModule.Array -> "Array"
    | Fidelity.PSG.IntrinsicModule.Math -> "Math"
    | Fidelity.PSG.IntrinsicModule.Unchecked -> "Unchecked"
    | Fidelity.PSG.IntrinsicModule.Operators -> "Operators"
    | Fidelity.PSG.IntrinsicModule.Parse -> "Parse"
    | Fidelity.PSG.IntrinsicModule.Format -> "Format"
    | Fidelity.PSG.IntrinsicModule.Convert -> "Convert"
    | Fidelity.PSG.IntrinsicModule.Crypto -> "Crypto"
    | Fidelity.PSG.IntrinsicModule.Bits -> "Bits"
    | Fidelity.PSG.IntrinsicModule.DateTime -> "DateTime"
    | Fidelity.PSG.IntrinsicModule.TimeSpan -> "TimeSpan"
    | Fidelity.PSG.IntrinsicModule.FnPtr -> "FnPtr"
    | Fidelity.PSG.IntrinsicModule.Mmio -> "Mmio"
    | Fidelity.PSG.IntrinsicModule.BorrowedView -> "BorrowedView"
    | Fidelity.PSG.IntrinsicModule.Lazy -> "Lazy"
    | Fidelity.PSG.IntrinsicModule.Seq -> "Seq"
    | Fidelity.PSG.IntrinsicModule.SeqEnumerator -> "SeqEnumerator"
    | Fidelity.PSG.IntrinsicModule.Arena -> "Arena"
    | Fidelity.PSG.IntrinsicModule.Platform -> "Platform"
    | Fidelity.PSG.IntrinsicModule.Map -> "Map"
    | Fidelity.PSG.IntrinsicModule.Set -> "Set"
    | Fidelity.PSG.IntrinsicModule.List -> "List"
    | Fidelity.PSG.IntrinsicModule.Option -> "Option"
    | Fidelity.PSG.IntrinsicModule.Result -> "Result"

let describeSemanticKind (kind: Fidelity.PSG.SemanticKind) : string =
    match kind with
    | Fidelity.PSG.SemanticKind.Binding(name, isMut, isRec, _) -> sprintf "Binding(%s, mut=%b, rec=%b)" name isMut isRec
    | Fidelity.PSG.SemanticKind.Application(fn, args) -> sprintf "Application(%d, [%s])" (nodeIdValue fn) (args |> List.map (nodeIdValue >> string) |> String.concat "; ")
    | Fidelity.PSG.SemanticKind.Lambda(_, body, _, enclosing, _) -> sprintf "Lambda(body=%d, enclosing=%s)" (nodeIdValue body) (Option.defaultValue "none" enclosing)
    | Fidelity.PSG.SemanticKind.Literal _ -> "Literal"
    | Fidelity.PSG.SemanticKind.VarRef(name, defOpt) -> sprintf "VarRef(%s, %s)" name (defOpt |> Option.map (nodeIdValue >> string) |> Option.defaultValue "none")
    | Fidelity.PSG.SemanticKind.Match(scrutinee, _) -> sprintf "Match(%d)" (nodeIdValue scrutinee)
    | Fidelity.PSG.SemanticKind.CaseElimination(scrutinee, _) -> sprintf "CaseElimination(%d)" (nodeIdValue scrutinee)
    | Fidelity.PSG.SemanticKind.Sequential nodes -> sprintf "Sequential([%s])" (nodes |> List.map (nodeIdValue >> string) |> String.concat "; ")
    | Fidelity.PSG.SemanticKind.WhileLoop(guard, body) -> sprintf "WhileLoop(%d, %d)" (nodeIdValue guard) (nodeIdValue body)
    | Fidelity.PSG.SemanticKind.ContinuationDispatch(sel, _, otherwise) -> sprintf "ContinuationDispatch(%d, otherwise=%d)" (nodeIdValue sel) (nodeIdValue otherwise)
    | Fidelity.PSG.SemanticKind.FrameRead(frame, slot) -> sprintf "FrameRead(%d, %d)" (nodeIdValue frame) (nodeIdValue slot)
    | Fidelity.PSG.SemanticKind.FrameBorrow(frame, slot) -> sprintf "FrameBorrow(%d, %d)" (nodeIdValue frame) (nodeIdValue slot)
    | Fidelity.PSG.SemanticKind.FrameWrite(frame, slot, v) -> sprintf "FrameWrite(%d, %d, %d)" (nodeIdValue frame) (nodeIdValue slot) (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.ContinuationStorage owner -> sprintf "ContinuationStorage(%d)" (nodeIdValue owner)
    | Fidelity.PSG.SemanticKind.ContinuationAllocate owner -> sprintf "ContinuationAllocate(%d)" (nodeIdValue owner)
    | Fidelity.PSG.SemanticKind.AggregateStorage source -> sprintf "AggregateStorage(%d)" (nodeIdValue source)
    | Fidelity.PSG.SemanticKind.DUInitialize(dest, caseName, caseIdx, _) -> sprintf "DUInitialize(%d, %s, %d)" (nodeIdValue dest) caseName caseIdx
    | Fidelity.PSG.SemanticKind.ClosureValue(impl, env) -> sprintf "ClosureValue(%d, %d)" (nodeIdValue impl) (nodeIdValue env)
    | Fidelity.PSG.SemanticKind.EnvironmentCreate(owner, _) -> sprintf "EnvironmentCreate(%d)" (nodeIdValue owner)
    | Fidelity.PSG.SemanticKind.EnvironmentAllocate owner -> sprintf "EnvironmentAllocate(%d)" (nodeIdValue owner)
    | Fidelity.PSG.SemanticKind.EnvironmentReference callable -> sprintf "EnvironmentReference(%d)" (nodeIdValue callable)
    | Fidelity.PSG.SemanticKind.EnvironmentRead(env, slot) -> sprintf "EnvironmentRead(%d, %d)" (nodeIdValue env) (nodeIdValue slot)
    | Fidelity.PSG.SemanticKind.EnvironmentBorrow(env, slot) -> sprintf "EnvironmentBorrow(%d, %d)" (nodeIdValue env) (nodeIdValue slot)
    | Fidelity.PSG.SemanticKind.EnvironmentWrite(env, slot, v) -> sprintf "EnvironmentWrite(%d, %d, %d)" (nodeIdValue env) (nodeIdValue slot) (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.ForLoop(var, start, finish, isUp, body) -> sprintf "ForLoop(%s, %d, %d, up=%b, %d)" var (nodeIdValue start) (nodeIdValue finish) isUp (nodeIdValue body)
    | Fidelity.PSG.SemanticKind.ForEach(var, _, coll, body) -> sprintf "ForEach(%s, %d, %d)" var (nodeIdValue coll) (nodeIdValue body)
    | Fidelity.PSG.SemanticKind.IfThenElse(guard, thenB, elseOpt) -> sprintf "IfThenElse(%d, %d, %s)" (nodeIdValue guard) (nodeIdValue thenB) (elseOpt |> Option.map (nodeIdValue >> string) |> Option.defaultValue "none")
    | Fidelity.PSG.SemanticKind.Require(cond, diag) -> sprintf "Require(%d, %s)" (nodeIdValue cond) diag
    | Fidelity.PSG.SemanticKind.TryWith(body, handler) -> sprintf "TryWith(%d, %d)" (nodeIdValue body) (nodeIdValue handler)
    | Fidelity.PSG.SemanticKind.TryFinally(body, cleanup) -> sprintf "TryFinally(%d, %d)" (nodeIdValue body) (nodeIdValue cleanup)
    | Fidelity.PSG.SemanticKind.RecordExpr _ -> "RecordExpr"
    | Fidelity.PSG.SemanticKind.UnionCase(name, idx, _) -> sprintf "UnionCase(%s, %d)" name idx
    | Fidelity.PSG.SemanticKind.DUGetTag(duVal, duTy) -> sprintf "DUGetTag(%d, %s)" (nodeIdValue duVal) (describeTypeIdentity duTy)
    | Fidelity.PSG.SemanticKind.DUEliminate(duVal, idx, name, _) -> sprintf "DUEliminate(%d, %d, %s)" (nodeIdValue duVal) idx name
    | Fidelity.PSG.SemanticKind.DUConstruct(name, idx, _, _) -> sprintf "DUConstruct(%s, %d)" name idx
    | Fidelity.PSG.SemanticKind.TupleExpr _ -> "TupleExpr"
    | Fidelity.PSG.SemanticKind.ArrayExpr _ -> "ArrayExpr"
    | Fidelity.PSG.SemanticKind.ArrayAllocate count -> sprintf "ArrayAllocate(%d)" (nodeIdValue count)
    | Fidelity.PSG.SemanticKind.ListExpr _ -> "ListExpr"
    | Fidelity.PSG.SemanticKind.FieldGet(expr, field) -> sprintf "FieldGet(%d, %s)" (nodeIdValue expr) field
    | Fidelity.PSG.SemanticKind.StringByteBorrow source -> sprintf "StringByteBorrow(%d)" (nodeIdValue source)
    | Fidelity.PSG.SemanticKind.FieldSet(expr, field, v) -> sprintf "FieldSet(%d, %s, %d)" (nodeIdValue expr) field (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.IndexGet(expr, idx) -> sprintf "IndexGet(%d, %d)" (nodeIdValue expr) (nodeIdValue idx)
    | Fidelity.PSG.SemanticKind.IndexSet(expr, idx, v) -> sprintf "IndexSet(%d, %d, %d)" (nodeIdValue expr) (nodeIdValue idx) (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.NamedIndexedPropertySet(expr, prop, idx, v) -> sprintf "NamedIndexedPropertySet(%d, %s, %d, %d)" (nodeIdValue expr) prop (nodeIdValue idx) (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.TypeAnnotation(expr, ty) -> sprintf "TypeAnnotation(%d, %s)" (nodeIdValue expr) (describeTypeIdentity ty)
    | Fidelity.PSG.SemanticKind.Upcast(expr, ty) -> sprintf "Upcast(%d, %s)" (nodeIdValue expr) (describeTypeIdentity ty)
    | Fidelity.PSG.SemanticKind.Downcast(expr, ty) -> sprintf "Downcast(%d, %s)" (nodeIdValue expr) (describeTypeIdentity ty)
    | Fidelity.PSG.SemanticKind.TypeTest(expr, ty) -> sprintf "TypeTest(%d, %s)" (nodeIdValue expr) (describeTypeIdentity ty)
    | Fidelity.PSG.SemanticKind.AddressOf(expr, isByref) -> sprintf "AddressOf(%d, byref=%b)" (nodeIdValue expr) isByref
    | Fidelity.PSG.SemanticKind.CellAddress binding -> sprintf "CellAddress(%d)" (nodeIdValue binding)
    | Fidelity.PSG.SemanticKind.ElementAddress(buf, idx) -> sprintf "ElementAddress(%d, %d)" (nodeIdValue buf) (nodeIdValue idx)
    | Fidelity.PSG.SemanticKind.FieldAddress(recv, field) -> sprintf "FieldAddress(%d, %s)" (nodeIdValue recv) field
    | Fidelity.PSG.SemanticKind.Reborrow refNode -> sprintf "Reborrow(%d)" (nodeIdValue refNode)
    | Fidelity.PSG.SemanticKind.Deref expr -> sprintf "Deref(%d)" (nodeIdValue expr)
    | Fidelity.PSG.SemanticKind.Set(target, v) -> sprintf "Set(%d, %d)" (nodeIdValue target) (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.PlatformBinding name -> sprintf "PlatformBinding(%s)" name
    | Fidelity.PSG.SemanticKind.Intrinsic info -> sprintf "Intrinsic(%s)" info.FullName
    | Fidelity.PSG.SemanticKind.TraitCall(memberName, _, arg) -> sprintf "TraitCall(%s, %d)" memberName (nodeIdValue arg)
    | Fidelity.PSG.SemanticKind.Quote(expr, isTyped) -> sprintf "Quote(%d, typed=%b)" (nodeIdValue expr) isTyped
    | Fidelity.PSG.SemanticKind.ObjectExpr(ty, _) -> sprintf "ObjectExpr(%s)" (describeTypeIdentity ty)
    | Fidelity.PSG.SemanticKind.ModuleDef(name, _) -> sprintf "ModuleDef(%s)" name
    | Fidelity.PSG.SemanticKind.TypeDef(name, _, _) -> sprintf "TypeDef(%s)" name
    | Fidelity.PSG.SemanticKind.MemberDef(name, _, _) -> sprintf "MemberDef(%s)" name
    | Fidelity.PSG.SemanticKind.InterpolatedString _ -> "InterpolatedString"
    | Fidelity.PSG.SemanticKind.PatternBinding name -> sprintf "PatternBinding(%s)" name
    | Fidelity.PSG.SemanticKind.LazyExpr(body, _) -> sprintf "LazyExpr(%d)" (nodeIdValue body)
    | Fidelity.PSG.SemanticKind.LazyForce lazyVal -> sprintf "LazyForce(%d)" (nodeIdValue lazyVal)
    | Fidelity.PSG.SemanticKind.EagerExpr operand -> sprintf "EagerExpr(%d)" (nodeIdValue operand)
    | Fidelity.PSG.SemanticKind.LazyValue(thunk, env) -> sprintf "LazyValue(%d, %d)" (nodeIdValue thunk) (nodeIdValue env)
    | Fidelity.PSG.SemanticKind.LazyEnvironment(owner, _) -> sprintf "LazyEnvironment(%d)" (nodeIdValue owner)
    | Fidelity.PSG.SemanticKind.LazyAllocate owner -> sprintf "LazyAllocate(%d)" (nodeIdValue owner)
    | Fidelity.PSG.SemanticKind.LazyEnvironmentReference lazyVal -> sprintf "LazyEnvironmentReference(%d)" (nodeIdValue lazyVal)
    | Fidelity.PSG.SemanticKind.LazyRead(env, slot) -> sprintf "LazyRead(%d, %d)" (nodeIdValue env) (nodeIdValue slot)
    | Fidelity.PSG.SemanticKind.LazyBorrow(env, slot) -> sprintf "LazyBorrow(%d, %d)" (nodeIdValue env) (nodeIdValue slot)
    | Fidelity.PSG.SemanticKind.LazyWrite(env, slot, v) -> sprintf "LazyWrite(%d, %d, %d)" (nodeIdValue env) (nodeIdValue slot) (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.SeqExpr(body, _) -> sprintf "SeqExpr(%d)" (nodeIdValue body)
    | Fidelity.PSG.SemanticKind.Yield v -> sprintf "Yield(%d)" (nodeIdValue v)
    | Fidelity.PSG.SemanticKind.YieldBang s -> sprintf "YieldBang(%d)" (nodeIdValue s)
    | Fidelity.PSG.SemanticKind.TupleGet(tuple, idx) -> sprintf "TupleGet(%d, %d)" (nodeIdValue tuple) idx
    | Fidelity.PSG.SemanticKind.Error msg -> sprintf "Error(%s)" msg
    | Fidelity.PSG.SemanticKind.Obligation info -> sprintf "Obligation(%s)" info.Id

let rec private describeValueRepresentation = function
    | Fidelity.PSG.ValueRepresentation.Scalar slot -> describeSettledSlot slot
    | Fidelity.PSG.ValueRepresentation.Buffer(None, elem) -> sprintf "buf<?x%s>" (describeValueRepresentation elem)
    | Fidelity.PSG.ValueRepresentation.Buffer(Some count, elem) -> sprintf "buf<%dx%s>" count (describeValueRepresentation elem)
    | Fidelity.PSG.ValueRepresentation.Record(fields, placement) ->
        let fs = fields |> List.map (fun (n, r) -> sprintf "%s: %s" n (describeValueRepresentation r)) |> String.concat "; "
        match placement with
        | Some(_, sz, al) -> sprintf "record<%s> (size=%d, align=%d)" fs sz al
        | None -> sprintf "record<%s> (unsettled)" fs
    | Fidelity.PSG.ValueRepresentation.CallableComponent(slot, data) ->
        sprintf "component(node %d: %s)" (nodeIdValue slot) (describeValueRepresentation data)
    | Fidelity.PSG.ValueRepresentation.Union(cases, placement) ->
        let cs =
            cases
            |> List.map (fun (name, ps) ->
                match ps with
                | [] -> name
                | _ -> sprintf "%s(%s)" name (ps |> List.map describeValueRepresentation |> String.concat ", "))
            |> String.concat " | "
        match placement with
        | Some(_, sz, al) -> sprintf "union<%s> (size=%d, align=%d)" cs sz al
        | None -> sprintf "union<%s> (unsettled)" cs
    | Fidelity.PSG.ValueRepresentation.Tag cases -> sprintf "tag<%d>" cases

/// Total deterministic type description for diagnostics (never throws or uses reflection formatting)
let rec describeType (ty: MLIRType) : string =
    match ty with
    | TInt (IntWidth bits) ->
        if bits > 0 then sprintf "i%d" bits else sprintf "i<unresolved:%d>" bits
    | TFloat width -> floatWidthToString width
    | TFunc (paramTypes, resultTypes) ->
        let paramStrs = paramTypes |> List.map describeType |> String.concat ", "
        let resultStrs = resultTypes |> List.map describeType |> String.concat ", "
        sprintf "(%s) -> (%s)" paramStrs resultStrs
    | TMemRef elemTy -> sprintf "memref<?x%s>" (describeType elemTy)
    | TMemRefStatic (size, elemTy) -> sprintf "memref<%dx%s>" size (describeType elemTy)
    | TMemRefScalar elemTy -> sprintf "memref<%s>" (describeType elemTy)
    | TVector (count, elemTy) -> sprintf "vector<%dx%s>" count (describeType elemTy)
    | TIndex -> "index"
    | TVoid -> "void"
    | TStruct (fields, Some bytes) ->
        let fieldStrs = fields |> List.map (fun (n, t) -> sprintf "%s: %s" n (describeType t)) |> String.concat "; "
        sprintf "struct<%s> (size=%d, align=%d)" fieldStrs bytes.Size bytes.Align
    | TStruct (fields, None) ->
        let fieldStrs = fields |> List.map (fun (n, t) -> sprintf "%s: %s" n (describeType t)) |> String.concat "; "
        sprintf "struct<%s> (unsettled)" fieldStrs
    | TSeqClock -> "!seq.clock"
    | TTag caseCount -> sprintf "tag<%d>" caseCount
    | TOpaqueHandle (handleType, bits, alignment) ->
        sprintf "opaque<%s, %d-bit, align=%d>" (describeTypeIdentity handleType) bits alignment
    | TResourceOption representation ->
        sprintf "resource-option<%s>" (describeValueRepresentation representation)

let describeTypeList (tys: MLIRType list) : string =
    tys |> List.map describeType |> String.concat ", " |> sprintf "[%s]"

let describeVisibility (visibility: FuncVisibility) : string =
    match visibility with
    | Public -> "public"
    | Private -> "private"

let describeByvalParams (byvalParams: ByvalParam list) : string =
    byvalParams
    |> List.map (fun p -> sprintf "param[%d](size=%d, align=%d)" p.ParamIndex p.SizeBytes p.AlignBytes)
    |> String.concat ", "
    |> sprintf "[%s]"

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
let private valToStringStep (pointer: Result<int, string>) (v: Val) : SerializationStep<string> =
    typeToStringStep pointer v.Type
    |> stepMap (sprintf "%s : %s" (ssaToString v.SSA))

let valToString (pointer: Result<int, string>) (v: Val) : Result<string, string> =
    valToStringStep pointer v |> stepToResult

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
let private arithOpToStringStep (pointer: Result<int, string>) (op: ArithOp) : SerializationStep<string> =
    let oneType ty fmt =
        typeToStringStep pointer ty |> stepMap fmt
    let twoTypes srcTy destTy fmt =
        stepPair (typeToStringStep pointer srcTy) (typeToStringStep pointer destTy) |> stepMap fmt
    match op with
    | ConstI (result, value, ty) ->
        oneType ty (sprintf "%s = arith.constant %s : %s" (ssaToString result) (string value))
    | ConstF (result, value, ty) ->
        oneType ty (sprintf "%s = arith.constant %f : %s" (ssaToString result) value)
    | AddI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.addi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | SubI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.subi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | MulI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.muli %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | DivSI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.divsi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | DivUI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.divui %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | RemSI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.remsi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | RemUI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.remui %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | AddF (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.addf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | SubF (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.subf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | NegF (result, operand, ty) ->
        oneType ty (sprintf "%s = arith.negf %s : %s" (ssaToString result) (ssaToString operand))
    | MulF (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.mulf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | DivF (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.divf %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CmpI (result, pred, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.cmpi %s, %s, %s : %s" (ssaToString result) (icmpPredToString pred) (ssaToString lhs) (ssaToString rhs))
    | CmpF (result, pred, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.cmpf %s, %s, %s : %s" (ssaToString result) (fcmpPredToString pred) (ssaToString lhs) (ssaToString rhs))
    | ExtSI (result, value, srcTy, destTy) ->
        twoTypes srcTy destTy (fun (s, d) -> sprintf "%s = arith.extsi %s : %s to %s" (ssaToString result) (ssaToString value) s d)
    | ExtUI (result, value, srcTy, destTy) ->
        twoTypes srcTy destTy (fun (s, d) -> sprintf "%s = arith.extui %s : %s to %s" (ssaToString result) (ssaToString value) s d)
    | ExtF (result, value, srcTy, destTy) ->
        twoTypes srcTy destTy (fun (s, d) -> sprintf "%s = arith.extf %s : %s to %s" (ssaToString result) (ssaToString value) s d)
    | TruncF (result, value, srcTy, destTy) ->
        twoTypes srcTy destTy (fun (s, d) -> sprintf "%s = arith.truncf %s : %s to %s" (ssaToString result) (ssaToString value) s d)
    | TruncI (result, value, srcTy, destTy) ->
        twoTypes srcTy destTy (fun (s, d) -> sprintf "%s = arith.trunci %s : %s to %s" (ssaToString result) (ssaToString value) s d)
    | SIToFP (result, value, srcTy, destTy) ->
        twoTypes srcTy destTy (fun (s, d) -> sprintf "%s = arith.sitofp %s : %s to %s" (ssaToString result) (ssaToString value) s d)
    | FPToSI (result, value, srcTy, destTy) ->
        twoTypes srcTy destTy (fun (s, d) -> sprintf "%s = arith.fptosi %s : %s to %s" (ssaToString result) (ssaToString value) s d)
    | Select (result, cond, trueVal, falseVal, ty) ->
        oneType ty (
            sprintf "%s = arith.select %s, %s, %s : %s"
                (ssaToString result) (ssaToString cond) (ssaToString trueVal) (ssaToString falseVal))
    // Bitwise operations (migrated from LLVM dialect)
    | AndI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.andi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | OrI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.ori %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | XorI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.xori %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | ShLI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.shli %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | ShRUI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.shrui %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | ShRSI (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = arith.shrsi %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))

let arithOpToString (pointer: Result<int, string>) (op: ArithOp) : Result<string, string> =
    arithOpToStringStep pointer op |> stepToResult

/// Serialize CombOp to CIRCT MLIR text (comb dialect)
/// Uses hwTypeToString: comb.* ops only appear on FPGA where TStruct → !hw.struct
let private combOpToStringStep (pointer: Result<int, string>) (op: CombOp) : SerializationStep<string> =
    let oneType ty fmt =
        hwTypeToStringStep pointer ty |> stepMap fmt
    match op with
    | CombAdd (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.add %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombSub (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.sub %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombMul (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.mul %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombDivS (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.divs %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombDivU (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.divu %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombMod (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.mods %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombModU (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.modu %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombAnd (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.and %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombOr (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.or %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombXor (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.xor %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombShl (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.shl %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombShrU (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.shru %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombShrS (result, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.shrs %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | CombICmp (result, pred, lhs, rhs, ty) ->
        oneType ty (sprintf "%s = comb.icmp %s %s, %s : %s" (ssaToString result) (icmpPredToString pred) (ssaToString lhs) (ssaToString rhs))
    | CombMux (result, cond, trueVal, falseVal, ty) ->
        oneType ty (sprintf "%s = comb.mux %s, %s, %s : %s" (ssaToString result) (ssaToString cond) (ssaToString trueVal) (ssaToString falseVal))

let combOpToString (pointer: Result<int, string>) (op: CombOp) : Result<string, string> =
    combOpToStringStep pointer op |> stepToResult

/// Serialize HWOp to CIRCT MLIR text (hw dialect)
/// Hardware module containers use the neutral frame grammar below.
let private hwOpToStringStep (pointer: Result<int, string>) (op: HWOp) : SerializationStep<string> =
    match op with
    | HWModule _ -> Refused "Hardware module serialization requires its neutral container frame."
    | HWOutput vals ->
        match vals with
        | [] -> Serialized "hw.output"
        | _ ->
            let valsStr = vals |> List.map (fun (ssa, _) -> ssaToString ssa) |> String.concat ", "
            stepMapList (fun (_, ty) -> hwTypeToStringStep pointer ty) vals
            |> stepMap (fun types ->
                let typesStr = String.concat ", " types
                sprintf "hw.output %s : %s" valsStr typesStr)
    | HWStructCreate (result, fieldVals, structTy) ->
        let valsStr = fieldVals |> List.map (fun (ssa, _) -> ssaToString ssa) |> String.concat ", "
        hwTypeToStringStep pointer structTy
        |> stepMap (sprintf "%s = hw.struct_create (%s) : %s" (ssaToString result) valsStr)
    | HWStructExtract (result, input, fieldName, structTy) ->
        hwTypeToStringStep pointer structTy
        |> stepMap (sprintf "%s = hw.struct_extract %s[\"%s\"] : %s" (ssaToString result) (ssaToString input) fieldName)
    | HWStructInject (result, input, fieldName, newValue, structTy) ->
        hwTypeToStringStep pointer structTy
        |> stepMap (sprintf "%s = hw.struct_inject %s[\"%s\"], %s : %s" (ssaToString result) (ssaToString input) fieldName (ssaToString newValue))
    | HWInstance (result, instName, moduleName, inputs, outputs) ->
        // hw.instance "instName" @moduleName(portName: %ssa : type, ...) -> (outName: type, ...)
        let inputsStep =
            stepMapList (fun (pn, ssa, ty) ->
                hwTypeToStringStep pointer ty
                |> stepMap (sprintf "%s: %s: %s" pn (ssaToString ssa))) inputs
        let outputsStep =
            stepMapList (fun (pn, ty) ->
                hwTypeToStringStep pointer ty
                |> stepMap (sprintf "%s: %s" pn)) outputs
        stepPair inputsStep outputsStep
        |> stepMap (fun (inList, outList) ->
            let inputsStr = String.concat ", " inList
            let outputsStr = String.concat ", " outList
            sprintf "%s = hw.instance \"%s\" @%s(%s) -> (%s)" (ssaToString result) instName moduleName inputsStr outputsStr)
    | HWAggregateConstant (result, structTy) ->
        let rec zeroLiteral (ty: MLIRType) : SerializationStep<string> =
            match ty with
            | TStruct (fields, _) ->
                stepMapList (fun (_, ft) -> zeroLiteral ft) fields
                |> stepMap (fun inner -> sprintf "[%s]" (String.concat ", " inner))
            | _ ->
                hwTypeToStringStep pointer ty
                |> stepMap (sprintf "0 : %s")
        let innerStep =
            match structTy with
            | TStruct (fields, _) ->
                stepMapList (fun (_, ft) -> zeroLiteral ft) fields
                |> stepMap (String.concat ", ")
            | _ -> zeroLiteral structTy
        stepPair innerStep (hwTypeToStringStep pointer structTy)
        |> stepMap (fun (innerStr, tyStr) ->
            sprintf "%s = hw.aggregate_constant [%s] : %s"
                (ssaToString result) innerStr tyStr)

let hwOpToString (pointer: Result<int, string>) (op: HWOp) : Result<string, string> =
    hwOpToStringStep pointer op |> stepToResult

/// Serialize SeqOp to CIRCT MLIR text (seq dialect)
let private seqOpToStringStep (pointer: Result<int, string>) (op: SeqOp) : SerializationStep<string> =
    match op with
    | SeqCompreg (result, input, clk, resetOpt, ty) ->
        typeToStringStep pointer ty
        |> stepMap (fun tyStr ->
            match resetOpt with
            | Some (resetSignal, resetValue) ->
                sprintf "%s = seq.compreg %s, %s reset %s, %s : %s"
                    (ssaToString result) (ssaToString input) (ssaToString clk)
                    (ssaToString resetSignal) (ssaToString resetValue) tyStr
            | None ->
                sprintf "%s = seq.compreg %s, %s : %s"
                    (ssaToString result) (ssaToString input) (ssaToString clk) tyStr)

let seqOpToString (pointer: Result<int, string>) (op: SeqOp) : Result<string, string> =
    seqOpToStringStep pointer op |> stepToResult

/// Serialize an SMT dialect type to MLIR text
let smtTypeToString (ty: SMTType) : string =
    match ty with
    | SMTBool -> "!smt.bool"
    | SMTInt -> "!smt.int"
    | SMTBV w -> sprintf "!smt.bv<%d>" w

/// Serialize SMTOp to MLIR text (verification modules)
let private smtOpToStringStep (pointer: Result<int, string>) (inner: MLIROp -> SerializationStep<string>) (op: SMTOp) : SerializationStep<string> =
    match op with
    | SMTSolver body ->
        stepMapList inner body
        |> stepMap (fun bodyList ->
            let bodyStr = String.concat "\n    " bodyList
            sprintf "smt.solver () : () -> () {\n    %s\n  }" bodyStr)
    | SMTSetLogic logic ->
        Serialized (sprintf "smt.set_logic \"%s\"" logic)
    | SMTDeclareFun (result, name, ty) ->
        Serialized (sprintf "%s = smt.declare_fun \"%s\" : %s" (ssaToString result) name (smtTypeToString ty))
    | SMTIntConstant (result, value) ->
        Serialized (sprintf "%s = smt.int.constant %d" (ssaToString result) value)
    | SMTBigIntConstant (result, value) ->
        Serialized (sprintf "%s = smt.int.constant %s" (ssaToString result) (string value))
    | SMTBVConstant (result, value, width) ->
        Serialized (sprintf "%s = smt.bv.constant #smt.bv<%d> : !smt.bv<%d>" (ssaToString result) value width)
    | SMTIntAdd (result, lhs, rhs) ->
        Serialized (sprintf "%s = smt.int.add %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | SMTIntSub (result, lhs, rhs) ->
        Serialized (sprintf "%s = smt.int.sub %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | SMTIntMod (result, lhs, rhs) ->
        Serialized (sprintf "%s = smt.int.mod %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | SMTIntDiv (result, lhs, rhs) ->
        Serialized (sprintf "%s = smt.int.div %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | SMTIntMul (result, lhs, rhs) ->
        Serialized (sprintf "%s = smt.int.mul %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
    | SMTIntCmp (result, pred, lhs, rhs) ->
        let predStr =
            match pred with
            | SmtLt -> "lt" | SmtLe -> "le" | SmtGt -> "gt" | SmtGe -> "ge"
        Serialized (sprintf "%s = smt.int.cmp %s %s, %s" (ssaToString result) predStr (ssaToString lhs) (ssaToString rhs))
    | SMTEq (result, lhs, rhs, ty) ->
        Serialized (sprintf "%s = smt.eq %s, %s : %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs) (smtTypeToString ty))
    | SMTAnd (result, operands) ->
        Serialized (sprintf "%s = smt.and %s" (ssaToString result) (operands |> List.map ssaToString |> String.concat ", "))
    | SMTOr (result, operands) ->
        Serialized (sprintf "%s = smt.or %s" (ssaToString result) (operands |> List.map ssaToString |> String.concat ", "))
    | SMTNot (result, operand) ->
        Serialized (sprintf "%s = smt.not %s" (ssaToString result) (ssaToString operand))
    | SMTIte (result, condition, thenValue, elseValue, ty) ->
        Serialized (
            sprintf "%s = smt.ite %s, %s, %s : %s" (ssaToString result) (ssaToString condition)
                (ssaToString thenValue) (ssaToString elseValue) (smtTypeToString ty))
    | SMTAssert operand ->
        Serialized (sprintf "smt.assert %s" (ssaToString operand))
    | SMTCheck ->
        Serialized "smt.check sat {} unknown {} unsat {}"

let smtOpToString (pointer: Result<int, string>) (inner: MLIROp -> Result<string, string>) (op: SMTOp) : Result<string, string> =
    smtOpToStringStep pointer (inner >> stepFromResult) op |> stepToResult

/// Serialize MemRefOp to MLIR text
let private memrefOpToStringStep (pointer: Result<int, string>) (op: MemRefOp) : SerializationStep<string> =
    match op with
    | MemRefOp.LoadAligned (result, memref, indices, _, memrefType, alignment) ->
        let indicesStr = indices |> List.map ssaToString |> String.concat ", "
        typeToStringStep pointer memrefType
        |> stepMap (
            sprintf "%s = memref.load %s[%s] {alignment = %d : i64} : %s"
                (ssaToString result) (ssaToString memref) indicesStr alignment)
    | MemRefOp.StoreAligned (value, memref, indices, _, memrefType, alignment) ->
        let indicesStr = indices |> List.map ssaToString |> String.concat ", "
        typeToStringStep pointer memrefType
        |> stepMap (
            sprintf "memref.store %s, %s[%s] {alignment = %d : i64} : %s"
                (ssaToString value) (ssaToString memref) indicesStr alignment)
    | MemRefOp.Load (result, memref, indices, _elemType, memrefType) ->
        // Build indices string
        let indicesStr = if List.isEmpty indices then "" else sprintf "[%s]" (indices |> List.map ssaToString |> String.concat ", ")
        // Use the passed memrefType directly (no heuristic reconstruction)
        typeToStringStep pointer memrefType
        |> stepMap (
            sprintf "%s = memref.load %s%s : %s"
                (ssaToString result) (ssaToString memref) indicesStr)
    | MemRefOp.Store (value, memref, indices, _elemType, memrefType) ->
        // Build indices string
        let indicesStr = if List.isEmpty indices then "" else sprintf "[%s]" (indices |> List.map ssaToString |> String.concat ", ")
        // Use the passed memrefType directly (no heuristic reconstruction)
        typeToStringStep pointer memrefType
        |> stepMap (
            sprintf "memref.store %s, %s%s : %s"
                (ssaToString value) (ssaToString memref) indicesStr)
    | MemRefOp.Alloca (result, memrefType, alignmentOpt) ->
        typeToStringStep pointer memrefType
        |> stepMap (fun tyStr ->
            match alignmentOpt with
            | Some alignment ->
                sprintf "%s = memref.alloca() {alignment = %d : i64} : %s"
                    (ssaToString result) alignment tyStr
            | None ->
                sprintf "%s = memref.alloca() : %s" (ssaToString result) tyStr)
    | MemRefOp.AllocaDynamic (result, count, elementType, alignment) ->
        typeToStringStep pointer (TMemRef elementType)
        |> stepMap (
            sprintf "%s = memref.alloca(%s) {alignment = %d : i64} : %s"
                (ssaToString result) (ssaToString count) alignment)
    | MemRefOp.Alloc (result, sizeSSA, elemType, alignmentOpt) ->
        // Heap allocation with runtime size: memref.alloc(%size) : memref<?xelemType>
        let memrefType = TMemRef elemType
        let alignment = alignmentOpt |> Option.map (sprintf " {alignment = %d : i64}") |> Option.defaultValue ""
        typeToStringStep pointer memrefType
        |> stepMap (
            sprintf "%s = memref.alloc(%s)%s : %s"
                (ssaToString result) (ssaToString sizeSSA) alignment)
    | MemRefOp.Dealloc (memref, memrefType) ->
        typeToStringStep pointer memrefType
        |> stepMap (sprintf "memref.dealloc %s : %s" (ssaToString memref))
    | MemRefOp.AllocStatic (result, memrefType, alignmentOpt) ->
        // Heap allocation with compile-time size: memref.alloc() : memref<NxT>
        // Like Alloca but heap-allocated — survives function return
        typeToStringStep pointer memrefType
        |> stepMap (fun tyStr ->
            match alignmentOpt with
            | Some alignment ->
                sprintf "%s = memref.alloc() {alignment = %d : i64} : %s"
                    (ssaToString result) alignment tyStr
            | None ->
                sprintf "%s = memref.alloc() : %s" (ssaToString result) tyStr)
    | MemRefOp.Copy (source, destination, sourceType, destinationType) ->
        stepPair (typeToStringStep pointer sourceType) (typeToStringStep pointer destinationType)
        |> stepMap (fun (srcStr, dstStr) ->
            sprintf "memref.copy %s, %s : %s to %s"
                (ssaToString source) (ssaToString destination) srcStr dstStr)
    | MemRefOp.SubView (result, source, offsets, resultType) ->
        let offsetsStr = offsets |> List.map ssaToString |> String.concat ", "
        typeToStringStep pointer resultType
        |> stepMap (
            sprintf "%s = memref.subview %s[%s] : %s"
                (ssaToString result) (ssaToString source) offsetsStr)
    | MemRefOp.SubViewSlice (result, source, offsets, sizes, strides, sourceType) ->
        // Proper MLIR memref.subview with 3 bracket groups: [offsets] [sizes] [strides]
        // Result has strided layout — callers must copy to contiguous buffer for FFI use.
        let fmtParam = function
            | SubViewParam.Static n -> string n
            | SubViewParam.Dynamic s -> ssaToString s
        let offsetsStr = offsets |> List.map ssaToString |> String.concat ", "
        let sizesStr = sizes |> List.map fmtParam |> String.concat ", "
        let stridesStr = strides |> List.map fmtParam |> String.concat ", "
        let elemTypeStep =
            match sourceType with
            | TMemRef t | TMemRefStatic (_, t) | TMemRefScalar t -> Serialized t
            | t -> Refused (sprintf "memref.subview: Alex emission did not supply a memref source for SSA %s: the source is typed %s" (ssaToString result) (describeType t))
        elemTypeStep
        |> stepBind (typeToStringStep pointer)
        |> stepBind (fun elemStr ->
            typeToStringStep pointer sourceType
            |> stepMap (fun srcTypeStr ->
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
                    srcTypeStr stridedTypeStr))
    | MemRefOp.ExtractBasePtr (result, memref, ty) ->
        // Extract pointer as platform word (index type) - PORTABLE!
        // Returns index (platform word size), caller must cast to target type if needed
        typeToStringStep pointer ty
        |> stepMap (
            sprintf "%s = memref.extract_aligned_pointer_as_index %s : %s -> index"
                (ssaToString result) (ssaToString memref))
    | MemRefOp.ExtractStridedMetadata(baseBuffer, offset, size, stride, source, sourceType, elementType) ->
        stepPair (typeToStringStep pointer sourceType) (typeToStringStep pointer (TMemRefScalar elementType))
        |> stepMap (fun (srcStr, elemStr) ->
            sprintf "%s, %s, %s, %s = memref.extract_strided_metadata %s : %s -> %s, index, index, index"
                (ssaToString baseBuffer) (ssaToString offset) (ssaToString size) (ssaToString stride)
                (ssaToString source) srcStr elemStr)
    | MemRefOp.GetGlobal (result, globalName, memrefType) ->
        // memref.get_global @symbol_name : memref<...>
        typeToStringStep pointer memrefType
        |> stepMap (
            sprintf "%s = memref.get_global @%s : %s"
                (ssaToString result) globalName)
    | MemRefOp.Dim (result, memref, index, memrefType) ->
        // memref.dim %memref, %index : memref<...>
        typeToStringStep pointer memrefType
        |> stepMap (
            sprintf "%s = memref.dim %s, %s : %s"
                (ssaToString result) (ssaToString memref) (ssaToString index))
    | MemRefOp.Cast (result, source, srcType, destType) ->
        // memref.cast %source : srcType to destType
        stepPair (typeToStringStep pointer srcType) (typeToStringStep pointer destType)
        |> stepMap (fun (srcStr, dstStr) ->
            sprintf "%s = memref.cast %s : %s to %s"
                (ssaToString result) (ssaToString source) srcStr dstStr)
    | MemRefOp.ReinterpretCast (result, source, byteOffset, size, srcType, destType) ->
        // One operation, one line. A view of another element type, or at a byte
        // offset, is MemRefOp.View with its offset value, composed by the Pattern.
        stepPair (typeToStringStep pointer srcType) (typeToStringStep pointer destType)
        |> stepMap (fun (srcStr, dstStr) ->
            sprintf "%s = memref.reinterpret_cast %s to offset: [%d], sizes: [%d], strides: [1] : %s to %s"
                (ssaToString result) (ssaToString source) byteOffset size srcStr dstStr)
    | MemRefOp.ReinterpretCastDynamic (result, source, offset, sizeSSA, srcType, destType) ->
        // memref.reinterpret_cast with dynamic size: reconstruct memref from pointer + known length
        // Used for string/array capture extraction where size is loaded from closure struct
        stepPair (typeToStringStep pointer srcType) (typeToStringStep pointer destType)
        |> stepMap (fun (srcStr, dstStr) ->
            sprintf "%s = memref.reinterpret_cast %s to offset: [%d], sizes: [%s], strides: [1] : %s to %s"
                (ssaToString result) (ssaToString source) offset (ssaToString sizeSSA) srcStr dstStr)
    | MemRefOp.View (result, source, offsetSSA, srcType, destType) ->
        // memref.view: typed view of byte buffer (different element type allowed)
        // Portable across all targets: CPU (→ GEP), FPGA (→ typed memory port), NPU (→ typed channel)
        stepPair (typeToStringStep pointer srcType) (typeToStringStep pointer destType)
        |> stepMap (fun (srcStr, dstStr) ->
            sprintf "%s = memref.view %s[%s][] : %s to %s"
                (ssaToString result) (ssaToString source) (ssaToString offsetSSA) srcStr dstStr)

let memrefOpToString (pointer: Result<int, string>) (op: MemRefOp) : Result<string, string> =
    memrefOpToStringStep pointer op |> stepToResult

/// Shared portable container grammar. Child holes contain operations, never
/// backend text or a callback that could introduce target instructions.
type ContainerPart =
    | Text of string
    | Children of prefix: string * separator: string * operations: MLIROp list
    | NamedChildren of prefix: string * separator: string * arguments: string list * operations: MLIROp list

let private withArgumentNames arguments text =
    arguments |> List.indexed |> List.rev
    |> List.fold (fun body (index, name) -> Alex.Text.replace (sprintf "%%arg%d" index) (sprintf "%%%s" name) body) text

let private containerFrameStep pointer = function
    | MLIROp.HWOp(HWModule(name, inputs, outputs, body)) ->
        let inputStep = inputs |> stepMapList (fun (n, ty) -> hwTypeToStringStep pointer ty |> stepMap (sprintf "in %%%s: %s" n))
        let outputStep = outputs |> stepMapList (fun (n, ty) -> hwTypeToStringStep pointer ty |> stepMap (sprintf "out %s: %s" n))
        stepPair inputStep outputStep
        |> stepMap (fun (inputPorts, outputPorts) ->
            Some [Text(sprintf "hw.module @%s(%s) {\n    " name (String.concat ", " (inputPorts @ outputPorts)))
                  NamedChildren("", "\n    ", List.map fst inputs, body); Text "\n}"])
    | MLIROp.FuncOp(FuncDef(name, args, resultTypes, body, _))
    | MLIROp.NoUnwindFunction(FuncDef(name, args, resultTypes, body, _)) as operation ->
        let argsStep = args |> stepMapList (fun (ssa, ty) -> typeToStringStep pointer ty |> stepMap (sprintf "%s: %s" (ssaToString ssa)))
        let resStep = resultTypesToStringStep pointer resultTypes
        let attributes = match operation with NoUnwindFunction _ -> " attributes {passthrough = [\"nounwind\"]}" | _ -> ""
        stepPair argsStep resStep
        |> stepMap (fun (argStrs, resStr) ->
            Some [Text(sprintf "func.func @%s(%s) -> %s%s {\n    " (symbolName name) (String.concat ", " argStrs) resStr attributes)
                  Children("", "\n    ", body); Text "\n}"])
    | MLIROp.SCFOp(SCFOp.While(condition, body)) ->
        Serialized (Some [Text "scf.while : () -> () {\n      "; Children("", "\n      ", condition)
                          Text "\n    } do {\n      "; Children("", "\n      ", body); Text "\n    }"])
    | MLIROp.SCFOp(SCFOp.If(condition, yes, no, result)) ->
        let resultStep =
            match result with
            | Some(ssa, ty) ->
                typeToStringStep pointer ty
                |> stepMap (fun tyStr -> sprintf "%s = " (ssaToString ssa), sprintf " -> (%s)" tyStr)
            | None -> Serialized ("", "")
        resultStep
        |> stepMap (fun (prefix, suffix) ->
            let first = [Text(sprintf "%sscf.if %s%s {\n      " prefix (ssaToString condition) suffix); Children("", "\n      ", yes)]
            Some(first @ (match no with
                          | Some body -> [Text "\n    } else {\n      "; Children("", "\n      ", body); Text "\n    }"]
                          | None -> [Text "\n    }"])))
    | MLIROp.SCFOp(SCFOp.For(induction, lower, upper, step, body)) ->
        Serialized (Some [Text(sprintf "scf.for %s = %s to %s step %s {\n      " (ssaToString induction) (ssaToString lower) (ssaToString upper) (ssaToString step))
                          Children("", "\n      ", body); Text "\n    }"])
    | MLIROp.SCFOp(SCFOp.IndexSwitch(selector, cases, fallback, results)) ->
        let resultsStep =
            match results with
            | [] -> Serialized ("", "")
            | _ ->
                let names = results |> List.map (fst >> ssaToString) |> String.concat ", "
                results
                |> stepMapList (snd >> typeToStringStep pointer)
                |> stepMap (fun types -> names + " = ", " -> " + String.concat ", " types)
        resultsStep
        |> stepMap (fun (prefix, resultTypes) ->
            let regions = (cases |> List.map (fun (label, body) -> sprintf "case %d" label, body)) @ ["default", fallback]
            let parts = regions |> List.mapi (fun index (label, body) ->
                [Text((if index = 0 then "" else "\n    ") + label + " {\n      "); Children("", "\n      ", body); Text "\n    }"]) |> List.concat
            Some(Text(sprintf "%sscf.index_switch %s%s\n    " prefix (ssaToString selector) resultTypes) :: parts))
    | _ -> Serialized None

let containerFrame pointer op : Result<ContainerPart list option, string> =
    containerFrameStep pointer op |> stepToResult

let moduleFrame moduleName operations =
    match moduleName with
    | Some name -> [Text(sprintf "module @%s {\n" name); Children("  ", "\n", operations); Text "\n}"]
    | None -> [Text "module {\n"; Children("  ", "\n", operations); Text "\n}"]

/// Serialize top-level MLIROp to portable MLIR text.
let rec private opToStringStep (pointer: Result<int, string>) (op: MLIROp) : SerializationStep<string> =
    match containerFrameStep pointer op with
    | RequiresTarget msg -> RequiresTarget msg
    | Refused err -> Refused err
    | Serialized (Some parts) ->
        parts
        |> stepMapList (function
            | Text text -> Serialized text
            | Children(prefix, separator, operations) ->
                operations
                |> stepMapList (fun child -> opToStringStep pointer child |> stepMap (fun s -> prefix + s))
                |> stepMap (String.concat separator)
            | NamedChildren(prefix, separator, arguments, operations) ->
                operations
                |> stepMapList (fun child -> opToStringStep pointer child |> stepMap (fun s -> prefix + s))
                |> stepMap (String.concat separator >> withArgumentNames arguments))
        |> stepMap (String.concat "")
    | Serialized None -> leafToStringStep pointer op

and private leafToStringStep (pointer: Result<int, string>) (op: MLIROp) : SerializationStep<string> =
    match op with
    | MLIROp.MmioLoad _ | MLIROp.MmioStore _ ->
        RequiresTarget "Portable MMIO intent requires realization by the selected backend."
    | MLIROp.ArithOp aop -> arithOpToStringStep pointer aop
    | MLIROp.MemRefOp mop -> memrefOpToStringStep pointer mop
    | MLIROp.NoUnwindFunction _ -> Refused "NoUnwindFunction requires a function definition"
    | MLIROp.FuncOp fop ->
        match fop with
        | FuncDef _ -> Refused "Function definition requires its portable container frame"
        | FuncDecl (name, paramTypes, resultTypes, _visibility, byvalParams) ->
            if not byvalParams.IsEmpty then
                Refused (sprintf "Foreign declaration '%s' requires a source-settled aggregate ABI realization; portable func declarations cannot realize byval metadata" name)
            else
                stepPair (stepMapList (typeToStringStep pointer) paramTypes) (resultTypesToStringStep pointer resultTypes)
                |> stepMap (fun (paramStrs, resStr) ->
                    sprintf "func.func private @%s(%s) -> %s" (symbolName name) (String.concat ", " paramStrs) resStr)
        | BoundaryFuncDecl (declaration, parameters, results) ->
            let rec containsBufferType = function
                | TMemRef _ | TMemRefStatic _ | TMemRefScalar _ -> true
                | TFunc(argTypes, retTypes) -> List.exists containsBufferType argTypes || List.exists containsBufferType retTypes
                | TVector(_, elemTy) -> containsBufferType elemTy
                | TStruct(fields, _) -> List.exists (snd >> containsBufferType) fields
                | _ -> false
            let requiresTargetMarshalling =
                (declaration.Parameters |> List.exists (fun (_, scalar) ->
                    match scalar with
                    | Fidelity.PSG.BoundaryScalar.WritableBytes _
                    | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes _
                    | Fidelity.PSG.BoundaryScalar.BorrowedBytes _ -> true
                    | _ -> false))
                || (declaration.Result |> Option.exists (function
                    | Fidelity.PSG.BoundaryScalar.BorrowedBytes _
                    | Fidelity.PSG.BoundaryScalar.WritableBytes _
                    | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes _ -> true
                    | _ -> false))
                || List.exists containsBufferType parameters
                || List.exists containsBufferType results
            if requiresTargetMarshalling then
                RequiresTarget "Boundary buffer and borrowed-view declarations require the selected backend and their exact source accounts."
            else
                stepPair (stepMapList (typeToStringStep pointer) parameters) (resultTypesToStringStep pointer results)
                |> stepMap (fun (paramStrs, resStr) ->
                    sprintf "func.func private @%s(%s) -> %s" (symbolName declaration.Symbol) (String.concat ", " paramStrs) resStr)
        | IntrinsicWriteDecl declaration ->
            match IntrinsicWriteAbi.parameters declaration, IntrinsicWriteAbi.results declaration with
            | Ok paramTys, Ok resTys ->
                stepPair (stepMapList (typeToStringStep pointer) paramTys) (resultTypesToStringStep pointer resTys)
                |> stepMap (fun (paramStrs, resStr) ->
                    sprintf "func.func private @%s(%s) -> %s" (symbolName declaration.Symbol) (String.concat ", " paramStrs) resStr)
            | Error err, _ | _, Error err -> Refused err
        | FuncCall (results, funcName, args) ->
            let argSSAs = args |> List.map (fun v -> ssaToString v.SSA) |> String.concat ", "
            stepPair (stepMapList (fun v -> typeToStringStep pointer v.Type) args) (resultTypesToStringStep pointer (List.map _.Type results))
            |> stepMap (fun (argTypeStrs, resStr) ->
                sprintf "%sfunc.call @%s(%s) : (%s) -> %s" (resultAssignment results) (symbolName funcName) argSSAs (String.concat ", " argTypeStrs) resStr)
        | FuncCallIndirect (results, callee, args) ->
            let argSSAs = args |> List.map (fun v -> ssaToString v.SSA) |> String.concat ", "
            stepPair (stepMapList (fun v -> typeToStringStep pointer v.Type) args) (resultTypesToStringStep pointer (List.map _.Type results))
            |> stepMap (fun (argTypeStrs, resStr) ->
                sprintf "%sfunc.call_indirect %s(%s) : (%s) -> %s" (resultAssignment results) (ssaToString callee) argSSAs (String.concat ", " argTypeStrs) resStr)
        | FuncConstant (result, funcName, funcTy) ->
            typeToStringStep pointer funcTy
            |> stepMap (sprintf "%s = func.constant @%s : %s" (ssaToString result) (symbolName funcName))
        | Return values ->
            match values with
            | [] -> Serialized "func.return"
            | _ ->
                if values |> List.exists (fun value -> value.Type = TVoid) then
                    Refused "Function return cannot contain a TVoid value"
                else
                    let operands = values |> List.map (fun value -> ssaToString value.SSA) |> String.concat ", "
                    values
                    |> stepMapList (fun value -> typeToStringStep pointer value.Type)
                    |> stepMap (fun types -> sprintf "func.return %s : %s" operands (String.concat ", " types))
    | MLIROp.GlobalString (name, content, storageLength, obligations) ->
        // Emit memref.global (portable MLIR) with null sentinel byte for C interop.
        // Clef strings are (ptr, length) — the sentinel is a storage detail invisible
        // to the type system, ensuring .Pointer yields C-compatible null-terminated data.
        let bytes = BAREWire.Encoding.Text.toUtf8 content
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
        Serialized (sprintf "memref.global \"private\" constant @%s : memref<%dxi8> = dense<[%s]>%s" name storageLength denseStr attrs)
    | MLIROp.GlobalBytePool (name, bytes, alignment, obligations) ->
        let dense = bytes |> List.map string |> String.concat ", "
        let anchors =
            match obligations with
            | [] -> ""
            | names -> sprintf ", clef.obligations = [%s]" (names |> List.map (sprintf "\"%s\"") |> String.concat ", ")
        Serialized (sprintf "memref.global \"private\" constant @%s : memref<%dxi8> = dense<[%s]> {alignment = %d : i64%s}"
            name bytes.Length dense alignment anchors)
    | MLIROp.GlobalMemref (name, memrefType, authority) ->
        // Zero-initialized static storage for a program-lifetime value (the program-lifetime
        // point of the lifetime lattice). Not `constant`: the closure struct is written into
        // this storage at construction. `uninitialized` is correct because every read is
        // preceded by the construction store; a heap-free target places this in .bss/Sram.
        match authority with
        | None ->
            Refused (sprintf "PSG settlement (program storage) did not settle a storage entry for the writable global @%s: an unowned global has no alignment to write" name)
        | Some entry ->
            let alignment = sprintf " {alignment = %d : i64}" entry.Alignment
            typeToStringStep pointer memrefType
            |> stepMap (fun tyStr -> sprintf "memref.global \"private\" @%s : %s = uninitialized%s" name tyStr alignment)
    | MLIROp.NativeEntrySlotDecl(_globalName, storage, entry, functionType) ->
        match storage.Shape, functionType with
        | Fidelity.PSG.ProgramStorageShape.NativeEntry formation, TFunc _ when formation = entry ->
            match NativeEntrySlotSymbols.names storage.Identity with
            | Error err -> Refused err
            | Ok (storeName, loadName) ->
                let slotType = TMemRefStatic(storage.Bytes, TInt(IntWidth 8))
                stepPair (typeToStringStep pointer slotType) (typeToStringStep pointer functionType)
                |> stepMap (fun (slotText, functionText) ->
                    sprintf
                        "func.func private @%s(%s, %s)\nfunc.func private @%s(%s) -> (%s)"
                        storeName slotText functionText loadName slotText functionText)
        | _ -> Refused "Native entry placeholder declaration differs from its typed source storage formation."
    | MLIROp.NativeEntrySlotStore(identity, _entry, destination, value) ->
        match destination.Type, value.Type with
        | TMemRefStatic(_, TInt(IntWidth 8)), TFunc _ ->
            match NativeEntrySlotSymbols.names identity with
            | Error err -> Refused err
            | Ok (storeName, _) ->
                stepPair (typeToStringStep pointer destination.Type) (typeToStringStep pointer value.Type)
                |> stepMap (fun (destTy, valTy) ->
                    sprintf
                        "func.call @%s(%s, %s) : (%s, %s) -> ()"
                        storeName (ssaToString destination.SSA) (ssaToString value.SSA) destTy valTy)
        | _ -> Refused "Native entry placeholder store requires its byte container and typed function value."
    | MLIROp.NativeEntrySlotLoad(identity, _entry, source, result) ->
        match source.Type, result.Type with
        | TMemRefStatic(_, TInt(IntWidth 8)), TFunc _ ->
            match NativeEntrySlotSymbols.names identity with
            | Error err -> Refused err
            | Ok (_, loadName) ->
                stepPair (typeToStringStep pointer source.Type) (typeToStringStep pointer result.Type)
                |> stepMap (fun (srcTy, resTy) ->
                    sprintf
                        "%s = func.call @%s(%s) : (%s) -> (%s)"
                        (ssaToString result.SSA) loadName (ssaToString source.SSA) srcTy resTy)
        | _ -> Refused "Native entry placeholder load requires its byte container and typed function result."
    | MLIROp.GlobalArray(name, memrefType, authority) ->
        let describeNativeLiteral = function
            | Fidelity.PSG.NativeLiteral.Int(value, _) -> sprintf "Int(%d)" value
            | Fidelity.PSG.NativeLiteral.UInt(value, _) -> sprintf "UInt(%u)" value
            | Fidelity.PSG.NativeLiteral.Float(value, _) -> sprintf "Float(%.17g)" value
            | Fidelity.PSG.NativeLiteral.String content -> sprintf "String(len=%d)" (String.length content)
            | Fidelity.PSG.NativeLiteral.Bool value -> sprintf "Bool(%b)" value
            | Fidelity.PSG.NativeLiteral.Char value -> sprintf "Char(0x%04x)" (int value)
            | Fidelity.PSG.NativeLiteral.Unit -> "Unit"
            | Fidelity.PSG.NativeLiteral.Decimal value -> sprintf "Decimal(%M)" value
            | Fidelity.PSG.NativeLiteral.ByteArray bytes -> sprintf "ByteArray(len=%d)" (Array.length bytes)
            | Fidelity.PSG.NativeLiteral.UInt16Array words -> sprintf "UInt16Array(len=%d)" (Array.length words)
        match authority.Initializers with
        | None -> Refused "Immutable array lacks its source-published initializer."
        | Some inits ->
            let formatInit = function
                | Fidelity.PSG.NativeLiteral.Int(value, _) -> Serialized (string value)
                | Fidelity.PSG.NativeLiteral.UInt(value, _) -> Serialized (string value)
                | Fidelity.PSG.NativeLiteral.Bool value -> Serialized (if value then "true" else "false")
                | Fidelity.PSG.NativeLiteral.Char value -> Serialized (string (int value))
                | Fidelity.PSG.NativeLiteral.Float(value, _) when value > -infinity && value < infinity ->
                    let text = sprintf "%.17g" value
                    Serialized (if text |> String.exists (fun c -> c = '.' || c = 'E' || c = 'e') then text else text + ".0")
                | other -> Refused (sprintf "Unsupported published array initializer: %s" (describeNativeLiteral other))
            stepPair (typeToStringStep pointer memrefType) (stepMapList formatInit inits)
            |> stepMap (fun (tyStr, values) ->
                sprintf "memref.global \"private\" constant @%s : %s = dense<[%s]> {alignment = %d : i64}"
                    name tyStr (String.concat ", " values) authority.Alignment)
    | MLIROp.IndexOp iop ->
        let describeIndexOp = function
            | IndexOp.IndexConst(r, v) -> sprintf "index.constant %s = %d" (ssaToString r) v
            | IndexOp.IndexBoolConst(r, v) -> sprintf "index.bool_constant %s = %b" (ssaToString r) v
            | IndexOp.IndexAdd(r, l, x) -> sprintf "index.add %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexSub(r, l, x) -> sprintf "index.sub %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexMul(r, l, x) -> sprintf "index.mul %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexDivS(r, l, x) -> sprintf "index.divs %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexDivU(r, l, x) -> sprintf "index.divu %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexCeilDivS(r, l, x) -> sprintf "index.ceildivs %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexCeilDivU(r, l, x) -> sprintf "index.ceildivu %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexFloorDivS(r, l, x) -> sprintf "index.floordivs %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexRemS(r, l, x) -> sprintf "index.rems %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexRemU(r, l, x) -> sprintf "index.remu %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexMaxS(r, l, x) -> sprintf "index.maxs %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexMaxU(r, l, x) -> sprintf "index.maxu %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexMinS(r, l, x) -> sprintf "index.mins %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexMinU(r, l, x) -> sprintf "index.minu %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexShl(r, l, x) -> sprintf "index.shl %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexShrS(r, l, x) -> sprintf "index.shrs %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexShrU(r, l, x) -> sprintf "index.shru %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexAnd(r, l, x) -> sprintf "index.and %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexOr(r, l, x) -> sprintf "index.or %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexXor(r, l, x) -> sprintf "index.xor %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexCmp(r, _, l, x) -> sprintf "index.cmp %s = (%s, %s)" (ssaToString r) (ssaToString l) (ssaToString x)
            | IndexOp.IndexCastS(r, o, src, dst) -> sprintf "index.casts %s = %s : %s -> %s" (ssaToString r) (ssaToString o) (describeType src) (describeType dst)
            | IndexOp.IndexCastU(r, o, src, dst) -> sprintf "index.castu %s = %s : %s -> %s" (ssaToString r) (ssaToString o) (describeType src) (describeType dst)
            | IndexOp.IndexSizeOf(r, ty) -> sprintf "index.sizeof %s : %s" (ssaToString r) (describeType ty)
        match iop with
        | IndexOp.IndexConst (result, value) ->
            Serialized (sprintf "%s = arith.constant %d : index" (ssaToString result) value)
        | IndexOp.IndexBoolConst (result, value) ->
            let boolVal = if value then 1 else 0
            Serialized (sprintf "%s = arith.constant %d : i1" (ssaToString result) boolVal)
        | IndexOp.IndexCastS (result, operand, srcTy, destTy) ->
            stepPair (typeToStringStep pointer srcTy) (typeToStringStep pointer destTy)
            |> stepMap (fun (srcStr, dstStr) -> sprintf "%s = index.casts %s : %s to %s" (ssaToString result) (ssaToString operand) srcStr dstStr)
        | IndexOp.IndexCastU (result, operand, srcTy, destTy) ->
            stepPair (typeToStringStep pointer srcTy) (typeToStringStep pointer destTy)
            |> stepMap (fun (srcStr, dstStr) -> sprintf "%s = index.castu %s : %s to %s" (ssaToString result) (ssaToString operand) srcStr dstStr)
        | IndexOp.IndexCmp (result, pred, lhs, rhs) ->
            let predStr =
                match pred with
                | Eq -> "eq" | Ne -> "ne"
                | Slt -> "slt" | Sle -> "sle"
                | Sgt -> "sgt" | Sge -> "sge"
                | Ult -> "ult" | Ule -> "ule"
                | Ugt -> "ugt" | Uge -> "uge"
            Serialized (sprintf "%s = index.cmp %s(%s, %s)" (ssaToString result) predStr (ssaToString lhs) (ssaToString rhs))
        | IndexOp.IndexAdd (result, lhs, rhs) ->
            Serialized (sprintf "%s = index.add %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
        | IndexOp.IndexMul (result, lhs, rhs) ->
            Serialized (sprintf "%s = index.mul %s, %s" (ssaToString result) (ssaToString lhs) (ssaToString rhs))
        | _ ->
            Refused (sprintf "backend (MLIR text) has no serialization for the index operation %s; it was emitted without one and is never written as a comment" (describeIndexOp iop))
    | MLIROp.Assert (condition, message) ->
        stringAttributeValue message
        |> stepFromResult
        |> stepMap (sprintf "cf.assert %s, \"%s\"" (ssaToString condition))
    | MLIROp.SCFOp scfOp ->
        match scfOp with
        | SCFOp.While _ | SCFOp.If _ | SCFOp.For _ | SCFOp.IndexSwitch _ ->
            Refused "Structured control flow requires its portable container frame"
        | SCFOp.Yield vals ->
            match vals with
            | [] -> Serialized "scf.yield"
            | _ ->
                let values = vals |> List.map (fst >> ssaToString) |> String.concat ", "
                vals
                |> stepMapList (snd >> typeToStringStep pointer)
                |> stepMap (fun types -> sprintf "scf.yield %s : %s" values (String.concat ", " types))
        | SCFOp.Condition (cond, args) ->
            let argsStr = args |> List.map ssaToString |> String.concat ", "
            Serialized (sprintf "scf.condition(%s) %s" (ssaToString cond) argsStr)
    | MLIROp.CombOp cop -> combOpToStringStep pointer cop
    | MLIROp.HWOp hop -> hwOpToStringStep pointer hop
    | MLIROp.SeqOp sop -> seqOpToStringStep pointer sop
    | MLIROp.SMTOp sop -> smtOpToStringStep pointer (opToStringStep pointer) sop
    | MLIROp.SpatialModule declaration ->
        let name,site,kind =
            match declaration with
            | Fidelity.PSG.SpatialModuleWitness.Hardware plan -> plan.Name,plan.Site,"hardware"
            | Fidelity.PSG.SpatialModuleWitness.Kernel plan -> plan.Name,plan.Site,"kernel"
        let (Fidelity.PSG.NodeId sourceId) = site
        Serialized (sprintf "module @%s attributes {clef.spatial_source = \"%d\", clef.spatial_kind = \"%s\"} {}"
            (symbolName name) sourceId kind)
    | MLIROp.WritableBufferCall _ ->
        RequiresTarget "Writable byte calls require the selected backend and their exact source accounts."
    | MLIROp.BoundaryBufferCall _ ->
        RequiresTarget "Boundary buffer and borrowed-view realization requires the selected backend and its exact source accounts."
    | MLIROp.EmptyBuffer _ | MLIROp.Utf8Validate _ | MLIROp.Utf8SnapshotRetire _ ->
        RequiresTarget "Checked text requires the selected backend and its exact snapshot, validator and retirement accounts."
    | MLIROp.OptionalEntryCall _ ->
        RequiresTarget "Optional entry calls require the selected backend and their exact source conversion accounts."
    | MLIROp.ResourceImport _ | MLIROp.ResourceCall _
    | MLIROp.ResourceOptionTag _ | MLIROp.ResourceOptionPayload _ | MLIROp.ResourceAlias _ ->
        RequiresTarget "Resource operations require the selected backend and their exact source accounts."
    | MLIROp.RawMLIR text -> portableText text |> stepFromResult
    | _ ->
        // Block and Region have no text form here: reaching one is a stop, never a comment.
        Refused (sprintf "backend (MLIR text) has no serialization for the operation %s; it was emitted without one and is never written as a comment" (describeMLIROp op))

and private describeMLIROp = function
    | MLIROp.EmptyBuffer(site, _) -> sprintf "EmptyBuffer(node %d)" (nodeIdValue site)
    | MLIROp.Utf8Validate(site, _, _) -> sprintf "Utf8Validate(node %d)" (nodeIdValue site)
    | MLIROp.Utf8SnapshotRetire(site, _) -> sprintf "Utf8SnapshotRetire(node %d)" (nodeIdValue site)
    | MLIROp.ResourceImport _ -> "ResourceImport"
    | MLIROp.ResourceCall(site, _, _) -> sprintf "ResourceCall(node %d)" (nodeIdValue site)
    | MLIROp.ResourceOptionTag(site, _, _) -> sprintf "ResourceOptionTag(node %d)" (nodeIdValue site)
    | MLIROp.ResourceOptionPayload(site, _, _) -> sprintf "ResourceOptionPayload(node %d)" (nodeIdValue site)
    | MLIROp.ResourceAlias(site, _) -> sprintf "ResourceAlias(node %d)" (nodeIdValue site)
    | MLIROp.WritableBufferCall(site, _, _) -> sprintf "WritableBufferCall(node %d)" (nodeIdValue site)
    | MLIROp.OptionalEntryCall(site, _, _, _) -> sprintf "OptionalEntryCall(node %d)" (nodeIdValue site)
    | MLIROp.BoundaryBufferCall(site, _, _, _, _) -> sprintf "BoundaryBufferCall(node %d)" (nodeIdValue site)
    | MLIROp.MmioLoad(site, r, _, bits) -> sprintf "MmioLoad(node %d, %s, i%d)" (nodeIdValue site) (ssaToString r) bits
    | MLIROp.MmioStore(site, v, _, bits) -> sprintf "MmioStore(node %d, %s, i%d)" (nodeIdValue site) (ssaToString v) bits
    | MLIROp.MemRefOp _ -> "MemRefOp"
    | MLIROp.ArithOp _ -> "ArithOp"
    | MLIROp.SCFOp _ -> "SCFOp"
    | MLIROp.Assert(cond, msg) -> sprintf "Assert(%s, %s)" (ssaToString cond) msg
    | MLIROp.NoUnwindFunction _ -> "NoUnwindFunction"
    | MLIROp.FuncOp _ -> "FuncOp"
    | MLIROp.IndexOp _ -> "IndexOp"
    | MLIROp.Block(label, ops) -> sprintf "Block(%s, %d ops)" label ops.Length
    | MLIROp.Region blocks -> sprintf "Region(%d blocks)" blocks.Length
    | MLIROp.SpatialModule _ -> "SpatialModule"
    | MLIROp.GlobalString(name, _, len, _) -> sprintf "GlobalString(%s, len=%d)" name len
    | MLIROp.GlobalBytePool(name, bytes, _, _) -> sprintf "GlobalBytePool(%s, len=%d)" name bytes.Length
    | MLIROp.GlobalMemref(name, ty, _) -> sprintf "GlobalMemref(%s : %s)" name (describeType ty)
    | MLIROp.NativeEntrySlotDecl(name, _, entry, ty) -> sprintf "NativeEntrySlotDecl(%s, node %d : %s)" name (nodeIdValue entry) (describeType ty)
    | MLIROp.NativeEntrySlotStore(_, entry, dst, _) -> sprintf "NativeEntrySlotStore(node %d, %s)" (nodeIdValue entry) (ssaToString dst.SSA)
    | MLIROp.NativeEntrySlotLoad(_, entry, src, _) -> sprintf "NativeEntrySlotLoad(node %d, %s)" (nodeIdValue entry) (ssaToString src.SSA)
    | MLIROp.GlobalArray(name, ty, _) -> sprintf "GlobalArray(%s : %s)" name (describeType ty)
    | MLIROp.CombOp _ -> "CombOp"
    | MLIROp.HWOp _ -> "HWOp"
    | MLIROp.SeqOp _ -> "SeqOp"
    | MLIROp.SMTOp _ -> "SMTOp"
    | MLIROp.RawMLIR _ -> "RawMLIR"

/// Serialize a list of operations with proper indentation
/// Serialize one op; a width failure inside it is annotated naming the op, so that the
/// stop says which value had no width rather than only that one did.
let private opToStringNamedStep (pointer: Result<int, string>) (op: MLIROp) : SerializationStep<string> =
    match opToStringStep pointer op |> stepBind (portableText >> stepFromResult) with
    | Refused message when Alex.Text.startsWith "Width inference failure" message ->
        Refused (message + "\nWhile serialising: " + describeMLIROp op)
    | other -> other

let opToString (pointer: Result<int, string>) (op: MLIROp) : Result<string, string> =
    opToStringStep pointer op |> stepToResult

let opsToString (pointer: Result<int, string>) (ops: MLIROp list) (indent: string) : Result<string, string> =
    ops
    |> stepMapList (opToStringNamedStep pointer)
    |> stepMap (fun lines -> lines |> List.map (fun line -> indent + line) |> String.concat "\n")
    |> stepToResult

/// Serialize a complete MLIR module
let private moduleToStringOptionStep (pointer: Result<int, string>) (moduleName: string option) (ops: MLIROp list) : SerializationStep<string> =
    moduleFrame moduleName ops
    |> stepMapList (function
        | Text text -> Serialized text
        | Children(prefix, separator, operations) ->
            operations
            |> stepMapList (fun child -> opToStringNamedStep pointer child |> stepMap (fun s -> prefix + s))
            |> stepMap (String.concat separator)
        | NamedChildren(prefix, separator, arguments, operations) ->
            operations
            |> stepMapList (fun child -> opToStringNamedStep pointer child |> stepMap (fun s -> prefix + s))
            |> stepMap (String.concat separator >> withArgumentNames arguments))
    |> stepMap (String.concat "")
    |> stepBind (portableText >> stepFromResult)

let moduleToString pointer moduleName operations : Result<string, string> =
    moduleToStringOptionStep pointer (Some moduleName) operations |> stepToResult

/// Validate every portable operation before reporting target deferral. A target
/// operation cannot hide a later serialization or source-width refusal.
let moduleText (pointer: Result<int, string>) (moduleName: string option) (ops: MLIROp list) : Result<ModuleText, string> =
    let validateFrame (parts: ContainerPart list) : SerializationStep<unit> =
        parts
        |> stepMapList (function
            | Text text -> portableText text |> stepFromResult |> stepMap ignore
            | Children(prefix, separator, _) | NamedChildren(prefix, separator, _, _) ->
                stepPair (portableText prefix |> stepFromResult) (portableText separator |> stepFromResult)
                |> stepMap ignore)
        |> stepMap ignore
    let headerCheck = validateFrame (moduleFrame moduleName ops)
    let bodyCheck =
        OperationStructure.flatten ops
        |> stepMapList (fun operation ->
            match containerFrameStep pointer operation with
            | Serialized (Some parts) -> validateFrame parts
            | Serialized None -> opToStringNamedStep pointer operation |> stepMap ignore
            | RequiresTarget msg -> RequiresTarget msg
            | Refused msg -> Refused msg)
    match stepPair headerCheck bodyCheck with
    | Refused err -> Error err
    | RequiresTarget _ -> Ok NeedsTargetRealization
    | Serialized _ ->
        match moduleToStringOptionStep pointer moduleName ops with
        | Serialized text -> Ok (Available text)
        | RequiresTarget _ -> Ok NeedsTargetRealization
        | Refused err -> Error err
