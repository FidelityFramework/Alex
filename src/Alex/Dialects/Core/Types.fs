/// Alex MLIR Type System
///
/// Structured MLIR type representation for Alex code generation.
/// This is the canonical type system used throughout Alex.
module Alex.Dialects.Core.Types

// ═══════════════════════════════════════════════════════════════════════════
// INTEGER AND FLOAT WIDTHS
// ═══════════════════════════════════════════════════════════════════════════

/// Integer bit width — arbitrary precision.
/// Width is a number, not an enum of CPU-blessed sizes.
/// MLIR natively supports iN for any N. CIRCT hw dialect supports arbitrary widths.
/// On FPGA, the width is exactly what the design needs — no more, no less.
[<Struct>]
type IntWidth = IntWidth of bits: int

/// Extract the bit count from an IntWidth
let inline intWidthBits (IntWidth bits) = bits

/// Size in bytes for a given bit width (ceiling division by 8)
let intWidthBytes (IntWidth bits) = (bits + 7) / 8

/// Floating-point widths supported by MLIR
type FloatWidth =
    | F32   // Single-precision
    | F64   // Double-precision

// ═══════════════════════════════════════════════════════════════════════════
// MLIR TYPE SYSTEM
// ═══════════════════════════════════════════════════════════════════════════

/// The settled byte layout of a struct on a core, read from the graph's settled layouts
/// (`SemanticGraph.Layouts`, Dimensional_Range_Design.md ruling 2): one offset per field in field
/// order, the size and the alignment. `None` on fabric, where a struct is an `hw.struct` value
/// with no byte layout. Composer reads these and computes none of them.
type StructBytes = { Offsets: int list; Size: int; Align: int }

/// Structured MLIR type representation
type MLIRType =
    | TInt of IntWidth
    | TFloat of FloatWidth
    | TFunc of MLIRType list * MLIRType list // Code value's function type (args, results); environment is separate
    | TMemRef of MLIRType                   // MemRef type (dynamic 1D)
    | TMemRefStatic of int * MLIRType       // Static-sized MemRef type (1D with known size)
    | TMemRefScalar of MLIRType             // Scalar MemRef type (0D)
    | TVector of int * MLIRType             // Vector type (SIMD)
    | TIndex                                // Index type
    | TVoid                                 // Foreign ABI: no returned value
    | TStruct of (string * MLIRType) list * StructBytes option   // Named struct type (record fields) and, on a core, its settled bytes
    | TSeqClock                             // CIRCT !seq.clock type (clock signal for registers)
    | TTag of int                           // DU tag discriminant (case count). Platform elision decides concrete width.
    /// An exact source-settled opaque resource value. This grants neither
    /// numeric/address operations nor spatial access and has no portable spelling.
    | TOpaqueHandle of handleType: Fidelity.PSG.TypeIdentity * bits: int * alignment: int
    /// Preserve the original settled resource-bearing union verbatim. Only the
    /// selected backend realizes its data; Alex owns no second layout.
    | TResourceOption of representation: Fidelity.PSG.ValueRepresentation

/// Shared physical vocabulary for a scalar slot already settled in the PSG.
/// Absence means this vocabulary has no admitted form; it supplies no default.
module SettledScalar =
    let tryType (slot: Fidelity.PSG.SettledSlot) =
        let inline integer bits = Some(TInt(IntWidth bits))
        match slot with
        | Fidelity.PSG.SettledSlot.Integer(bits, _) when bits > 0 -> integer bits
        | Fidelity.PSG.SettledSlot.Bool -> integer 1
        | Fidelity.PSG.SettledSlot.Char -> integer 32
        | Fidelity.PSG.SettledSlot.Real 32 -> Some(TFloat F32)
        | Fidelity.PSG.SettledSlot.Real 64 -> Some(TFloat F64)
        | Fidelity.PSG.SettledSlot.Pointer 1 -> Some TIndex
        | Fidelity.PSG.SettledSlot.Unit -> integer 32
        | Fidelity.PSG.SettledSlot.CHandle(handleType, bits, alignment) when bits > 0 && alignment > 0 ->
            Some(TOpaqueHandle(handleType, bits, alignment))
        | _ -> None

// ═══════════════════════════════════════════════════════════════════════════
// PLATFORM TYPES
// ═══════════════════════════════════════════════════════════════════════════

/// Target operating system family
type OSFamily =
    | Linux
    | Windows
    | MacOS
    | FreeBSD

/// The target architecture as Composer reads it (plan D8, L-10; Dimensional_Range_Design.md
/// §8.3): the width dimensions the platform description declares,
/// `Register` and `Pointer`, read once from the CCS context (MLIRGeneration.architectureOf). There
/// is no architecture table: a width the description does not declare carries CCS8203's text,
/// and the site that needs it fails with that text, never with a number of its own. An FPGA
/// description declares neither, and no site on the fabric leg reads them.
type Architecture = {
    Register: Result<int, string>
    Pointer: Result<int, string>
}

/// The platform's word: the declared Register width as an MLIR integer width.
let declaredWordWidth (arch: Architecture) : Result<IntWidth, string> =
    arch.Register |> Result.map IntWidth

// The declared Pointer width in bytes: the size of an index, and the unit of a memref
// descriptor (five words). Function code values have no implicit data-storage layout.
let declaredPointerBytes (arch: Architecture) : Result<int, string> =
    arch.Pointer |> Result.map (fun bits -> (bits + 7) / 8)

// The size in bytes of a value as it is stored: a read, never a computation (§8.3, one size
// model). A scalar is the bytes of its selected width; every pointer-sized type (an index; a
// rank-1 memref descriptor, {allocPtr, alignPtr, offset, size, stride}, five words)
// is the declared Pointer width times its words, and `pointer` is `Error`
// where no declaration is in hand (serialization), so that a pointer-sized value reaching such a
// path is a loud defect and never a silent eight bytes; a struct is its settled size, read from
// the layout CCS settled at saturation, and a struct with none (fabric, an opaque field) is a
// stop. A width the range was to give (`IntWidth 0`) has no size and is a stop naming it.
let rec mlirTypeSizeWith (pointer: Result<int, string>) (ty: MLIRType) : Result<int, string> =
    let pointerBytes () =
        pointer |> Result.map (fun bits -> (bits + 7) / 8)
    match ty with
    | TInt (IntWidth 0) -> Error "mlirTypeSize: an integer whose width the node's range was to give reached a size read unnarrowed"
    | TInt w -> Ok (intWidthBytes w)
    | TFloat F32 -> Ok 4 | TFloat F64 -> Ok 8
    | TOpaqueHandle _ | TResourceOption _ -> Error "mlirTypeSize: an opaque resource cannot acquire generic spatial storage authority"
    | TFunc _ -> Error "mlirTypeSize: a function code SSA has no admitted data-storage layout; settle callable storage before sizing it"
    | TMemRef _ | TMemRefStatic _ | TMemRefScalar _ -> pointerBytes () |> Result.map (fun bytes -> 5 * bytes)
    | TVector (count, _) ->
        Error (sprintf "mlirTypeSize: PSG settlement (Layouts) did not settle a storage size for a vector of %d lanes; no size is read for it" count)
    | TIndex -> pointerBytes ()
    | TStruct (_, Some bytes) -> Ok bytes.Size
    | TStruct (fields, None) ->
        Error (sprintf "mlirTypeSize: the struct {%s} has no settled layout to read its size from (a fabric struct, or a field the placement could not settle)"
            (fields |> List.map fst |> String.concat ", "))
    | TSeqClock -> Error "mlirTypeSize: a clock signal (!seq.clock) has no byte storage; a fabric value reached a size read"
    | TTag caseCount ->
        Error (sprintf "mlirTypeSize: backend (CIRCT) did not settle a byte size for the abstract tag of %d cases: a fabric tag's width is the hw backend's, and a core holds a tag as a byte memref" caseCount)
    | TVoid -> Error "mlirTypeSize: TVoid marks a foreign function with no result; it is not a value and has no size"

// The settled byte offset of a struct's field, read from the layout CCS settled; a struct with
// no settled layout, or a field outside it, is a stop.
let structFieldOffset (ty: MLIRType) (fieldIndex: int) : Result<int, string> =
    match ty with
    | TStruct (_, Some bytes) ->
        match List.tryItem fieldIndex bytes.Offsets with
        | Some offset -> Ok offset
        | None -> Error (sprintf "structFieldOffset: field %d is outside the settled layout of %d fields" fieldIndex bytes.Offsets.Length)
    | TStruct (fields, None) ->
        Error (sprintf "structFieldOffset: the struct {%s} has no settled layout to read an offset from" (fields |> List.map fst |> String.concat ", "))
    | _ -> Error "structFieldOffset: the supplied type is not a struct"

// The size model read through the architecture's declared Pointer width.
let mlirTypeSize (arch: Architecture) (ty: MLIRType) : Result<int, string> =
    mlirTypeSizeWith arch.Pointer ty

// ═══════════════════════════════════════════════════════════════════════════
// SSA VALUES AND BLOCK REFERENCES
// ═══════════════════════════════════════════════════════════════════════════

/// SSA value reference - the currency of MLIR operations
/// V = value from computation, Arg = function/block argument
/// A value name. `V (node, k)` is the k-th value emission names for a graph node, a pure
/// derivation from the node's identity (Alex.Traversal.Values); `Arg n` a block argument. No
/// pass assigns names and no witness holds a counter: the graph identifies the node, the witness
/// numbers what it emits for it.
[<Struct>]
type SSA =
    | V of node: int * ordinal: int   // %v<node>_<k>
    | CallableAlternative of node: int * alternative: int // Source-settled mutable read dispatch arm
    | AggregateComponent of node: int * slot: int * alternative: int * lane: int
    | ArrayElementIndex of node: int * element: int // Unbounded literal element ordinal, disjoint from local temporaries
    | Arg of int                      // %arg0, %arg1, ...

/// Block label reference
[<Struct>]
type BlockRef = BlockRef of string

/// A typed SSA value (value + its type)
type Val = {
    SSA: SSA
    Type: MLIRType
}

/// Create a typed value
let val' ssa ty = { SSA = ssa; Type = ty }

// ═══════════════════════════════════════════════════════════════════════════
// COMPARISON PREDICATES
// ═══════════════════════════════════════════════════════════════════════════

/// Integer comparison predicates (for arith.cmpi)
type ICmpPred =
    | Eq | Ne                       // Equal, Not equal
    | Slt | Sle | Sgt | Sge         // Signed comparisons
    | Ult | Ule | Ugt | Uge         // Unsigned comparisons

/// Float comparison predicates (for arith.cmpf)
type FCmpPred =
    // Ordered comparisons (return false if either operand is NaN)
    | OEq | ONe | OLt | OLe | OGt | OGe
    // Unordered comparisons (return true if either operand is NaN)
    | UEq | UNe | ULt | ULe | UGt | UGe
    // Special predicates
    | Ord   // Ordered (neither operand is NaN)
    | Uno   // Unordered (either operand is NaN)
    // False/True (always)
    | AlwaysFalse | AlwaysTrue

/// Index comparison predicates (for index.cmp)
type IndexCmpPred =
    | Eq | Ne                       // Equal, Not equal
    | Slt | Sle | Sgt | Sge         // Signed comparisons
    | Ult | Ule | Ugt | Uge         // Unsigned comparisons

// ═══════════════════════════════════════════════════════════════════════════
// MEMORY ORDERING AND VISIBILITY
// ═══════════════════════════════════════════════════════════════════════════

/// Function visibility for external linking
type FuncVisibility =
    | Public                        // Visible to all modules
    | Private                       // Visible only within module

// ═══════════════════════════════════════════════════════════════════════════
// MLIR OPERATIONS (for type-safe MLIR construction)
// ═══════════════════════════════════════════════════════════════════════════

/// Dimension parameter for memref.subview: compile-time constant or runtime SSA value
[<RequireQualifiedAccess>]
type SubViewParam =
    | Static of int64
    | Dynamic of SSA

/// MemRef dialect operations (standard MLIR memory operations)
type MemRefOp =
    | Load of SSA * SSA * SSA list * MLIRType * MLIRType               // result, memref, indices, elemType, memrefType
    | Store of SSA * SSA * SSA list * MLIRType * MLIRType              // value, memref, indices, elemType, memrefType
    | LoadAligned of SSA * SSA * SSA list * MLIRType * MLIRType * int // explicit byte alignment, including packed fields
    | StoreAligned of SSA * SSA * SSA list * MLIRType * MLIRType * int
    /// Standard contiguous representation copy. This confers no source-value
    /// initialization or current-read evidence on the destination.
    | Copy of source: SSA * destination: SSA * sourceType: MLIRType * destinationType: MLIRType
    | Alloca of SSA * MLIRType * int option                            // result, memrefType, alignment (stack, compile-time size)
    | AllocaDynamic of result: SSA * count: SSA * elementType: MLIRType * alignment: int
    | Alloc of SSA * SSA * MLIRType * int option                       // result, sizeSSA, elementType, alignment (heap, runtime size)
    | Dealloc of SSA * MLIRType                                        // owned heap memref, released after its last use
    | AllocStatic of SSA * MLIRType * int option                        // result, memrefType, alignment (heap, compile-time size)
    | SubView of SSA * SSA * SSA list * MLIRType                       // result, source, offsets, resultType (legacy element access)
    | SubViewSlice of SSA * SSA * SSA list * SubViewParam list * SubViewParam list * MLIRType  // result, source, offsets, sizes, strides, sourceType (proper MLIR 3-group, strided result)
    | ExtractBasePtr of SSA * SSA * MLIRType                           // result, memref, memrefType → !llvm.ptr (for FFI)
    /// One rank-one descriptor's base buffer, element offset, extent and stride.
    | ExtractStridedMetadata of baseBuffer: SSA * offset: SSA * size: SSA * stride: SSA * source: SSA * sourceType: MLIRType * elementType: MLIRType
    | GetGlobal of SSA * string * MLIRType                             // result, globalName, memrefType
    | Dim of SSA * SSA * SSA * MLIRType                                // result, memref, dimIndex, memrefType (returns index)
    | Cast of SSA * SSA * MLIRType * MLIRType                          // result, source, srcType, destType (memref type cast)
    | ReinterpretCast of SSA * SSA * int * int * MLIRType * MLIRType   // result, source, byteOffset, size, srcType, destType
    | ReinterpretCastDynamic of SSA * SSA * int * SSA * MLIRType * MLIRType  // result, source, offset, sizeSSA, srcType, destType (dynamic size for memref reconstruction)
    | View of SSA * SSA * SSA * MLIRType * MLIRType                   // result, source, offsetSSA, srcType, destType (different element type: byte buffer → typed view)

/// Arithmetic dialect operations
type ArithOp =
    // Constants
    | ConstI of SSA * bigint * MLIRType                     // result, exact value, type
    | ConstF of SSA * float * MLIRType                      // result, value, type
    // Integer arithmetic
    | AddI of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | SubI of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | MulI of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | DivSI of SSA * SSA * SSA * MLIRType                   // result, lhs, rhs, type (signed)
    | DivUI of SSA * SSA * SSA * MLIRType                   // result, lhs, rhs, type (unsigned)
    | RemSI of SSA * SSA * SSA * MLIRType                   // result, lhs, rhs, type (signed)
    | RemUI of SSA * SSA * SSA * MLIRType                   // result, lhs, rhs, type (unsigned)
    | CmpI of SSA * ICmpPred * SSA * SSA * MLIRType         // result, predicate, lhs, rhs, type
    // Float arithmetic
    | AddF of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | SubF of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | NegF of SSA * SSA * MLIRType                          // result, operand, type
    | MulF of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | DivF of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | CmpF of SSA * FCmpPred * SSA * SSA * MLIRType         // result, predicate, lhs, rhs, type
    // Type conversions
    | ExtSI of SSA * SSA * MLIRType * MLIRType              // result, value, srcType, destType
    | ExtUI of SSA * SSA * MLIRType * MLIRType              // result, value, srcType, destType
    | ExtF of SSA * SSA * MLIRType * MLIRType
    | TruncF of SSA * SSA * MLIRType * MLIRType
    | TruncI of SSA * SSA * MLIRType * MLIRType             // result, value, srcType, destType
    | SIToFP of SSA * SSA * MLIRType * MLIRType             // result, value, srcType, destType
    | FPToSI of SSA * SSA * MLIRType * MLIRType             // result, value, srcType, destType
    // Bitwise operations (migrated from LLVM dialect)
    | AndI of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | OrI of SSA * SSA * SSA * MLIRType                     // result, lhs, rhs, type
    | XorI of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | ShLI of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type (shift left)
    | ShRUI of SSA * SSA * SSA * MLIRType                   // result, lhs, rhs, type (logical shift right)
    | ShRSI of SSA * SSA * SSA * MLIRType                   // result, lhs, rhs, type (arithmetic shift right)
    // Other
    | Select of SSA * SSA * SSA * SSA * MLIRType            // result, cond, trueVal, falseVal, type

/// Index dialect operations
type IndexOp =
    | IndexConst of SSA * int64                       // result, value
    | IndexBoolConst of SSA * bool                    // result, value
    | IndexAdd of SSA * SSA * SSA                     // result, lhs, rhs
    | IndexSub of SSA * SSA * SSA                     // result, lhs, rhs
    | IndexMul of SSA * SSA * SSA                     // result, lhs, rhs
    | IndexDivS of SSA * SSA * SSA                    // result, lhs, rhs (signed)
    | IndexDivU of SSA * SSA * SSA                    // result, lhs, rhs (unsigned)
    | IndexCeilDivS of SSA * SSA * SSA                // result, lhs, rhs (signed ceiling)
    | IndexCeilDivU of SSA * SSA * SSA                // result, lhs, rhs (unsigned ceiling)
    | IndexFloorDivS of SSA * SSA * SSA               // result, lhs, rhs (signed floor)
    | IndexRemS of SSA * SSA * SSA                    // result, lhs, rhs (signed)
    | IndexRemU of SSA * SSA * SSA                    // result, lhs, rhs (unsigned)
    | IndexMaxS of SSA * SSA * SSA                    // result, lhs, rhs (signed)
    | IndexMaxU of SSA * SSA * SSA                    // result, lhs, rhs (unsigned)
    | IndexMinS of SSA * SSA * SSA                    // result, lhs, rhs (signed)
    | IndexMinU of SSA * SSA * SSA                    // result, lhs, rhs (unsigned)
    | IndexShl of SSA * SSA * SSA                     // result, lhs, rhs
    | IndexShrS of SSA * SSA * SSA                    // result, lhs, rhs (signed)
    | IndexShrU of SSA * SSA * SSA                    // result, lhs, rhs (unsigned)
    | IndexAnd of SSA * SSA * SSA                     // result, lhs, rhs
    | IndexOr of SSA * SSA * SSA                      // result, lhs, rhs
    | IndexXor of SSA * SSA * SSA                     // result, lhs, rhs
    | IndexCmp of SSA * IndexCmpPred * SSA * SSA      // result, predicate, lhs, rhs
    | IndexCastS of SSA * SSA * MLIRType * MLIRType    // result, operand, srcType, destType (signed)
    | IndexCastU of SSA * SSA * MLIRType * MLIRType    // result, operand, srcType, destType (unsigned)
    | IndexSizeOf of SSA * MLIRType                   // result, type

/// CIRCT Combinational Logic Dialect (pure, stateless operations)
/// Maps to hw/comb dialect — synthesizable combinational logic for FPGA targets
type CombOp =
    // Integer arithmetic (combinational — no clock, no state)
    | CombAdd of SSA * SSA * SSA * MLIRType                    // result, lhs, rhs, type
    | CombSub of SSA * SSA * SSA * MLIRType
    | CombMul of SSA * SSA * SSA * MLIRType
    | CombDivS of SSA * SSA * SSA * MLIRType                   // signed
    | CombDivU of SSA * SSA * SSA * MLIRType                   // unsigned
    | CombMod of SSA * SSA * SSA * MLIRType                    // signed (comb.mods)
    | CombModU of SSA * SSA * SSA * MLIRType                   // unsigned (comb.modu)
    // Bitwise
    | CombAnd of SSA * SSA * SSA * MLIRType
    | CombOr of SSA * SSA * SSA * MLIRType
    | CombXor of SSA * SSA * SSA * MLIRType
    | CombShl of SSA * SSA * SSA * MLIRType
    | CombShrU of SSA * SSA * SSA * MLIRType
    | CombShrS of SSA * SSA * SSA * MLIRType
    // Comparison
    | CombICmp of SSA * ICmpPred * SSA * SSA * MLIRType        // result, pred, lhs, rhs, type
    // Multiplexer (if/else → combinational select)
    | CombMux of SSA * SSA * SSA * SSA * MLIRType              // result, cond, trueVal, falseVal, type

/// CIRCT Sequential Logic Dialect (clocked state, registers)
/// Maps to seq dialect — flip-flops and clocked elements for FPGA targets
type SeqOp =
    | SeqCompreg of SSA * SSA * SSA * (SSA * SSA) option * MLIRType    // result, input, clk, (resetSignal, resetValue) option, type

/// SMT dialect types (upstream `smt` dialect, adopted from CIRCT).
/// Used ONLY inside verification modules — never mixes with program value types.
type SMTType =
    | SMTBool
    | SMTInt
    | SMTBV of int          // bit-vector width

/// Integer comparison predicates for smt.int.cmp
type SMTCmpPred =
    | SmtLt | SmtLe | SmtGt | SmtGe

/// Portable text is unavailable when a structured operation requires target realization.
type ModuleText =
    | Available of string
    | NeedsTargetRealization

/// One source-selected optional entry arm. Absence supplies no code value.
type OptionalEntryArm = {
    CaseOrdinal: int
    Claim: Fidelity.PSG.NodeId
    Code: Val option
}

[<RequireQualifiedAccess>]
type OptionalEntrySlotChoice =
    | Direct of OptionalEntryArm
    | Conditional of selection: Fidelity.PSG.NodeId * tag: Val * whenTrue: OptionalEntryArm * whenFalse: OptionalEntryArm

/// One source-selected optional entry position. The original Option operand
/// stays in the call vector; any retained closed formation stays typed until target realization.
type OptionalEntrySlot = {
    Ordinal: int
    Choice: OptionalEntrySlotChoice
}

/// One source-selected optional byte-buffer arm. Absence converts None strictly
/// to a boundary null carrier while keeping interior fat pointers non-null.
type BufferAbsenceArm = {
    CaseOrdinal: int
    Claim: Fidelity.PSG.NodeId
    Buffer: Val option
}

[<RequireQualifiedAccess>]
type BufferAbsenceSlotChoice =
    | Direct of BufferAbsenceArm
    | Conditional of selection: Fidelity.PSG.NodeId * tag: Val * whenTrue: BufferAbsenceArm * whenFalse: BufferAbsenceArm

/// One source-selected optional byte-buffer position converting None at the boundary.
type BufferAbsenceSlot = {
    BufferOrdinal: int
    Plan: BufferAbsenceSlotChoice
}

/// Top-level portable operation. Target dialects belong to backend realization.
/// Single-phase execution with nested accumulators - no scope markers needed
type MLIROp =
    /// The source proves this exact byte snapshot has zero extent and no
    /// backing instance. Descriptor realization belongs to the selected target.
    | EmptyBuffer of site: Fidelity.PSG.NodeId * result: Val
    /// Validation observes only the source-issued independent byte snapshot.
    /// The selected backend supplies the named validator's operational semantics.
    | Utf8Validate of site: Fidelity.PSG.NodeId * snapshot: Val * result: Val
    /// Logical retirement under the source-issued snapshot residence; this is
    /// never permission to infer a heap free.
    | Utf8SnapshotRetire of site: Fidelity.PSG.NodeId * snapshot: Val
    /// Resource operations preserve the original source incidence. Their opaque
    /// values have no portable stock spelling; only a selected backend with the
    /// current conversion and cleanup accounts may realize them.
    | ResourceImport of declaration: Fidelity.PSG.BoundaryImport
    | ResourceCall of site: Fidelity.PSG.NodeId * arguments: Val list * result: Val option
    | ResourceOptionTag of site: Fidelity.PSG.NodeId * source: Val * result: Val option
    | ResourceOptionPayload of site: Fidelity.PSG.NodeId * source: Val * result: Val
    | ResourceAlias of site: Fidelity.PSG.NodeId * source: Val
    /// Direct writable borrowing retains the exact source call occurrence and
    /// complete native argument order. Target address realization is deferred.
    | WritableBufferCall of site: Fidelity.PSG.NodeId * arguments: Val list * result: Val option
    /// Source-selected Some conversion, deferred to the selected backend.
    /// Slots retain their original ordinal, case and per-use proof citizen.
    | OptionalEntryCall of site: Fidelity.PSG.NodeId * arguments: Val list * slots: OptionalEntrySlot list * results: Val list
    /// Direct read-only buffer, boundary buffer-absence, or borrowed
    /// result-view call retaining the exact source occurrence and native
    /// operand order. Target address, null-boundary, and staging realization
    /// are deferred to the selected backend.
    | BoundaryBufferCall of site: Fidelity.PSG.NodeId * arguments: Val list * optionalEntries: OptionalEntrySlot list * bufferAbsences: BufferAbsenceSlot list * results: Val list
    /// Published MMIO intent retains its exact source account; target expansion
    /// and any temporary values belong to the selected backend.
    | MmioLoad of site: Fidelity.PSG.NodeId * result: SSA * address: SSA * bits: int
    | MmioStore of site: Fidelity.PSG.NodeId * value: SSA * address: SSA * bits: int
    | MemRefOp of MemRefOp
    | ArithOp of ArithOp
    | SCFOp of SCFOp
    /// A required runtime boundary check; failure terminates before the foreign access.
    | Assert of condition: SSA * message: string
    /// MCU functions terminate on failure; unwinding across the exception
    /// adapter is unsupported. Applied only to definitions, never foreign declarations.
    | NoUnwindFunction of FuncOp
    | FuncOp of FuncOp
    | IndexOp of IndexOp
    | Block of string * MLIROp list                                 // label, ops
    | Region of MLIROp list                                         // blocks
    /// Inert portable declaration; complete source plan remains correlated in
    /// the catalog until the selected backend realizes its target module.
    | SpatialModule of Fidelity.PSG.SpatialModuleWitness
    // Module-level declarations (backend-agnostic)
    | GlobalString of name: string * content: string * byteLength: int * obligations: string list  // obligations: anchor names of the obligations constraining this storage (PHG 2.4b), reified as {clef.obligations = [...]}
    /// One immutable allocation whose bytes and alignment were settled in the PSG.
    | GlobalBytePool of name: string * bytes: byte list * alignment: int * obligations: string list
    /// Exact source inventory accompanies writable storage. None identifies a
    /// legacy unowned declaration; it cannot pass storage correspondence.
    | GlobalMemref of string * MLIRType * Fidelity.PSG.ProgramStorageEntry option
    /// Compiler-internal typed placeholders retain the original slot/entry
    /// correspondence until the selected target realizes its code-pointer cell.
    | NativeEntrySlotDecl of
        globalName: string *
        storage: Fidelity.PSG.ProgramStorageEntry *
        entry: Fidelity.PSG.NodeId *
        functionType: MLIRType
    | NativeEntrySlotStore of identity: Fidelity.PSG.ProgramStorageIdentity * entry: Fidelity.PSG.NodeId * destination: Val * value: Val
    | NativeEntrySlotLoad of identity: Fidelity.PSG.ProgramStorageIdentity * entry: Fidelity.PSG.NodeId * source: Val * result: Val
    /// Exact immutable initializer and residence authority settled by Baker.
    | GlobalArray of string * MLIRType * Fidelity.PSG.MemoryArrayLiteralWitness
    // CIRCT hardware dialects (FPGA targets)
    | CombOp of CombOp
    | HWOp of HWOp
    | SeqOp of SeqOp
    // SMT dialect (verification modules — proof obligations as IR)
    | SMTOp of SMTOp
    // Raw MLIR text (dialect-opaque: AIE, GPU, etc.)
    | RawMLIR of string

/// Structured Control Flow (SCF) dialect operations
and SCFOp =
    | If of SSA * MLIROp list * MLIROp list option * (SSA * MLIRType) option  // cond, thenOps, elseOps, result (None = void)
    | IndexSwitch of selector: SSA * cases: (int64 * MLIROp list) list * defaultBody: MLIROp list * results: (SSA * MLIRType) list
    | While of MLIROp list * MLIROp list                      // condOps, bodyOps
    /// `induction` is the value the operation defines for its body.
    | For of induction: SSA * lower: SSA * upper: SSA * step: SSA * body: MLIROp list
    | Yield of (SSA * MLIRType) list                          // values with types
    | Condition of SSA * SSA list                             // cond, args

/// Control Flow (CF) dialect operations - unstructured control flow
/// passed via `byval` — the struct data goes on the stack, not in a register.
and ByvalParam = { ParamIndex: int; SizeBytes: int; AlignBytes: int }

/// Function dialect operations
and FuncOp =
    // Function definition/declaration
    | FuncDef of string * (SSA * MLIRType) list * MLIRType list * MLIROp list * FuncVisibility  // name, args, resultTypes, body, visibility
    | FuncDecl of string * MLIRType list * MLIRType list * FuncVisibility * ByvalParam list     // name, paramTypes, resultTypes, visibility, byvalParams (external decl)
    /// Exact source boundary contract accompanies its portable physical spelling.
    /// Signedness and calling convention remain available to target realization.
    | BoundaryFuncDecl of Fidelity.PSG.BoundaryImport * MLIRType list * MLIRType list
    /// Source-settled intrinsic authority, distinct from a foreign C declaration.
    | IntrinsicWriteDecl of Fidelity.PSG.IntrinsicWriteImport
    // Function calls
    | FuncCall of Val list * string * Val list                                             // results, func, args
    | FuncCallIndirect of Val list * SSA * Val list                                        // results, callee, args
    | FuncConstant of SSA * string * MLIRType                                              // result, funcName, funcType
    // Return
    | Return of Val list                                                                  // ordered typed results

/// CIRCT Hardware Construction Dialect (structural, module-level)
/// Maps to hw dialect — hardware modules, instances, and ports for FPGA targets
and HWOp =
    | HWModule of string * (string * MLIRType) list * (string * MLIRType) list * MLIROp list
      // name, inputs (name*type), outputs (name*type), body
    | HWOutput of (SSA * MLIRType) list
    // Struct operations (hw.struct_create, hw.struct_extract, hw.struct_inject)
    | HWStructCreate of SSA * (SSA * MLIRType) list * MLIRType
      // result, field values (ssa * fieldType), structType
    | HWStructExtract of SSA * SSA * string * MLIRType
      // result, input, fieldName, structType
    | HWStructInject of SSA * SSA * string * SSA * MLIRType
      // result, input, fieldName, newValue, structType
    // Module instantiation (hw.instance)
    | HWInstance of SSA * string * string * (string * SSA * MLIRType) list * (string * MLIRType) list
      // result, instanceName, moduleName, inputs (portName*ssa*type), outputs (portName*type)
    // Aggregate constant (hw.aggregate_constant) — zero-initialize structs
    | HWAggregateConstant of SSA * MLIRType
      // result, structType (all fields zero-initialized)

/// SMT dialect operations (upstream `smt` dialect — proof obligations as IR).
/// Emitted into verification modules by SMTTransfer; exported to SMT-LIB via
/// mlir-translate --export-smtlib. Solver-neutral: any SMT-LIB solver dispatches.
and SMTOp =
    | SMTSolver of MLIROp list                      // smt.solver () : () -> () { body }
    | SMTSetLogic of string                         // smt.set_logic "QF_LIA"
    | SMTDeclareFun of SSA * string * SMTType       // result, name (exported verbatim), type
    | SMTIntConstant of SSA * int64                 // smt.int.constant
    | SMTBigIntConstant of SSA * bigint             // exact unbounded smt.int.constant
    | SMTBVConstant of SSA * int64 * int            // result, value, width
    | SMTIntAdd of SSA * SSA * SSA                  // result, lhs, rhs
    | SMTIntSub of SSA * SSA * SSA                  // result, lhs, rhs
    | SMTIntMod of SSA * SSA * SSA                  // result, lhs, rhs
    | SMTIntDiv of SSA * SSA * SSA                  // result, lhs, rhs (integer quotient)
    | SMTIntMul of SSA * SSA * SSA                  // result, lhs, rhs
    | SMTIntCmp of SSA * SMTCmpPred * SSA * SSA     // result, predicate, lhs, rhs
    | SMTEq of SSA * SSA * SSA * SMTType            // result, lhs, rhs, operand type
    | SMTAnd of SSA * SSA list                      // result, operands (variadic)
    | SMTOr of SSA * SSA list                       // result, operands (variadic)
    | SMTNot of SSA * SSA                           // result, operand
    | SMTIte of SSA * SSA * SSA * SSA * SMTType     // result, condition, then, else, result type
    | SMTAssert of SSA                              // assert a !smt.bool value
    | SMTCheck                                      // smt.check sat {} unknown {} unsat {}

module BoundaryAbi =
    let private optionalEntryPresentArmAt (revision: Fidelity.PSG.Revision)
                                          (call: Fidelity.PSG.BoundaryCall) ordinal
                                          (operand: Fidelity.PSG.BoundaryOperand)
                                          (selected: Fidelity.PSG.BoundaryOptionalEntry)
                                          missing =
        match selected.Payload, selected.Formation, operand.Abi,
              revision.CurrentClaims.TryFind selected.Obligation with
        | Some payload, Some formation, Fidelity.PSG.BoundaryScalar.Entry invocation, Some claim
            when List.contains claim revision.Obligations ->
            match claim.Body with
            | Fidelity.PSG.ObligationBody.OptionalEntryArgumentConversion model when
                revision.Emission.Boundary.Calls.TryFind call.Site = Some call
                && List.tryItem ordinal call.Arguments = Some operand
                && claim.Kind = sprintf "foreign-optional-entry-conversion-%d" ordinal
                && selected.CaseOrdinal = 1 && model.SourceCase = selected.CaseOrdinal
                && model.Call = call.Site && model.Parameter = ordinal
                && model.Actual = operand.Actual && model.Construction = selected.Construction
                && model.Payload = payload && model.Formation = formation && model.Invocation = invocation ->
                Ok(selected, claim, model)
            | _ -> Error missing
        | _ -> Error missing

    let private optionalEntryAbsentArmAt (revision: Fidelity.PSG.Revision)
                                         (call: Fidelity.PSG.BoundaryCall) ordinal
                                         (operand: Fidelity.PSG.BoundaryOperand)
                                         (selected: Fidelity.PSG.BoundaryOptionalEntry)
                                         missing
                                         stalePrefix =
        if selected.CaseOrdinal <> 0 || selected.Payload.IsSome || selected.Formation.IsSome then
            Error missing
        else
            match operand.Abi, revision.CurrentClaims.TryFind selected.Obligation with
            | Fidelity.PSG.BoundaryScalar.Entry invocation, Some claim when List.contains claim revision.Obligations ->
                match claim.Body with
                | Fidelity.PSG.ObligationBody.OptionalEntryAbsenceArgumentConversion model when
                    revision.Emission.Boundary.Calls.TryFind call.Site = Some call
                    && List.tryItem ordinal call.Arguments = Some operand
                    && claim.Kind = sprintf "foreign-optional-entry-conversion-%d" ordinal
                    && model.SourceCase = 0 && model.Call = call.Site && model.Parameter = ordinal
                    && model.Actual = operand.Actual && model.Construction = selected.Construction ->
                    match revision.Emission.Boundary.CallbackAbsences.TryFind model.Absence with
                    | Some absence when absence.Quote = model.Absence && absence.Import = call.Import
                                        && absence.Parameter = ordinal && absence.Formal = operand.Formal
                                        && absence.Invocation = invocation
                                        && (revision.Emission.Boundary.Imports.TryFind call.Import
                                            |> Option.bind (fun imp -> imp.Parameters |> List.tryFindIndex (fun (f, _) -> f = absence.Formal)) = Some ordinal) ->
                        match Fidelity.PSG.Integrity.check revision with
                        | [] ->
                            Fidelity.PSG.OptionalEntryArgumentProof.projectAbsence model
                            |> Result.map (fun _ -> selected, claim, model, absence)
                        | violations -> Error (stalePrefix + Fidelity.PSG.Integrity.describe violations)
                    | _ -> Error missing
                | _ -> Error missing
            | _ -> Error missing

    /// Read the current per-use source plan. This does not realize a native
    /// address or treat the source solver receipt as target discharge.
    let optionalEntryConversionAt (revision: Fidelity.PSG.Revision)
                                  (call: Fidelity.PSG.BoundaryCall) ordinal
                                  (operand: Fidelity.PSG.BoundaryOperand) =
        let missing = "Optional native-entry boundary conversion requires target-pathway authority; this consumer does not admit it."
        match operand.OptionalEntry with
        | Some (Fidelity.PSG.BoundaryOptionalEntryChoice.Direct selected) ->
            optionalEntryPresentArmAt revision call ordinal operand selected missing
        | Some (Fidelity.PSG.BoundaryOptionalEntryChoice.Conditional _) | None -> Error missing

    /// Absence has its own current per-use account. It supplies no callable
    /// formation, payload or native null value to the portable witness.
    let optionalEntryAbsenceConversionAt (revision: Fidelity.PSG.Revision)
                                         (call: Fidelity.PSG.BoundaryCall) ordinal
                                         (operand: Fidelity.PSG.BoundaryOperand) =
        let missing = "Optional native-entry absence conversion lacks its exact current source account."
        match operand.OptionalEntry with
        | Some (Fidelity.PSG.BoundaryOptionalEntryChoice.Direct selected) ->
            optionalEntryAbsentArmAt
                revision call ordinal operand selected missing
                "Optional native-entry absence conversion has stale published source facts: "
        | _ -> Error missing

    /// Validate settled CHandle and Option<CHandle> representations without
    /// deriving admission from nominal declaration names or synthesizing alignment.
    let matchesCHandleRepresentation (nullable: bool) (expectedHandleType: Fidelity.PSG.TypeIdentity option) (expectedBits: int option) (rep: Fidelity.PSG.ValueRepresentation) =
        let matchesSlot = function
            | Fidelity.PSG.ValueRepresentation.Scalar(Fidelity.PSG.SettledSlot.CHandle(ht, bits, alignment)) ->
                bits > 0 && alignment > 0
                && (expectedHandleType |> Option.forall ((=) ht))
                && (expectedBits |> Option.forall ((=) bits))
            | _ -> false
        if not nullable then matchesSlot rep
        else
            match rep with
            | Fidelity.PSG.ValueRepresentation.Union(cases, Some(_, bytes, optAlign)) when
                cases.Length = 2 && bytes > 0 && optAlign > 0 ->
                (cases |> List.filter (snd >> List.isEmpty) |> List.length) = 1
                && (cases |> List.filter (fun (_, payloads) ->
                    match payloads with
                    | [p] -> matchesSlot p
                    | _ -> false) |> List.length) = 1
            | _ -> false

    let private settledRepresentationForTypeAndNode (revision: Fidelity.PSG.Revision) (nodeOpt: Fidelity.PSG.NodeId option) (ty: Fidelity.PSG.TypeIdentity) =
        let byNode = nodeOpt |> Option.bind revision.Emission.Numeric.OccurrenceRepresentations.TryFind
        let byType = revision.Emission.Numeric.TypeRepresentations.TryFind ty
        match byNode, byType with
        | Some(Ok r1), Some(Ok r2) when r1 = r2 -> Some r1
        | Some(Ok r1), None -> Some r1
        | None, Some(Ok r2) -> Some r2
        | _ -> None

    let borrowedCHandleRepAt (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) (formal: Fidelity.PSG.NodeId) (nullable: bool) =
        if not (imp.DeclarationFacts.ContainsKey formal) then None
        else
            imp.SourceTypes.TryFind formal
            |> Option.bind (settledRepresentationForTypeAndNode revision (Some formal))
            |> Option.filter (matchesCHandleRepresentation nullable None None)

    let callbackHandleRepAt (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) (formal: Fidelity.PSG.NodeId) (ordinal: int) (nullable: bool) =
        let isSettledOptionalWrapper (optTy: Fidelity.PSG.TypeIdentity) =
            match settledRepresentationForTypeAndNode revision (Some formal) optTy with
            | Some (Fidelity.PSG.ValueRepresentation.Union(cases, Some(_, bytes, optAlign)))
                when cases.Length = 2 && bytes > 0 && optAlign > 0 ->
                let emptyCount = cases |> List.filter (snd >> List.isEmpty) |> List.length
                let singleCount = cases |> List.filter (fun (_, ps) -> ps.Length = 1) |> List.length
                emptyCount = 1 && singleCount = 1
            | _ -> false
        let unwrapEntryFnType = function
            | Fidelity.PSG.TypeIdentity.Application(entry, [fnTy])
                when entry.NativeKind = Some Fidelity.PSG.NTUKind.NTUfnptr -> Some fnTy
            | Fidelity.PSG.TypeIdentity.Application(opt, [ Fidelity.PSG.TypeIdentity.Application(entry, [fnTy]) ]) as optTy
                when opt.NativeKind.IsNone && entry.NativeKind = Some Fidelity.PSG.NTUKind.NTUfnptr
                     && isSettledOptionalWrapper optTy -> Some fnTy
            | _ -> None
        let rec domainTypes = function
            | Fidelity.PSG.TypeIdentity.Function(Fidelity.PSG.TypeIdentity.Tuple(_, domains), _) -> domains
            | Fidelity.PSG.TypeIdentity.Function(domain, range) -> domain :: domainTypes range
            | _ -> []
        if not (imp.DeclarationFacts.ContainsKey formal) then None
        else
            imp.SourceTypes.TryFind formal
            |> Option.bind unwrapEntryFnType
            |> Option.map domainTypes
            |> Option.bind (List.tryItem ordinal)
            |> Option.bind (settledRepresentationForTypeAndNode revision None)
            |> Option.filter (matchesCHandleRepresentation nullable None None)

    let private claimBodyAt (revision: Fidelity.PSG.Revision) (id: Fidelity.PSG.NodeId) (expectedKind: string) =
        match revision.CurrentClaims.TryFind id with
        | Some info when info.Kind = expectedKind && List.contains info revision.Obligations -> Some info
        | _ -> None

    let private conditionalTagSelectionAt (revision: Fidelity.PSG.Revision)
                                          (call: Fidelity.PSG.BoundaryCall)
                                          (operand: Fidelity.PSG.BoundaryOperand)
                                          (selection: Fidelity.PSG.NodeId)
                                          (tagProjection: Fidelity.PSG.NodeId)
                                          missing =
        let tagCurrent =
            match revision.Nodes.TryFind tagProjection, revision.Nodes.TryFind operand.Actual with
            | Some { Kind = Fidelity.PSG.SemanticKind.DUGetTag(tagTarget, unionType); Children = [tagChild]; Type = tagType; ValueRange = tagRange },
              Some actualNode ->
                tagTarget = operand.Actual
                && tagChild = operand.Actual
                && unionType = actualNode.Type
                && tagRange = Some(Fidelity.PSG.ValueRange.Bounded(0I, 1I))
                && call.Participants.Contains tagProjection
                && (revision.Nodes.TryFind call.Site |> Option.exists (fun siteNode -> List.contains tagProjection siteNode.Children))
                && (revision.Emission.Numeric.Values.TryFind tagProjection
                    |> Option.exists (fun carrier ->
                        carrier.Site = tagProjection
                        && carrier.SourceType = tagType
                        && carrier.Range = Fidelity.PSG.ValueRange.Bounded(0I, 1I)
                        && carrier.Participants.Contains operand.Actual))
            | _ -> false
        let selections =
            revision.Emission.Callable.AggregateValues.TryFind selection
            |> Option.defaultValue []
            |> List.filter (fun row -> row.Operation = Fidelity.PSG.CallableAggregateOperation.Select)
        match selections with
        | [selectedRow] when tagCurrent && operand.Adaptation.IsNone && selectedRow.Occurrence = selection && selectedRow.Aggregate = selection ->
            Ok selectedRow
        | _ -> Error missing

    let optionalEntryConditionalAt (revision: Fidelity.PSG.Revision)
                                           (call: Fidelity.PSG.BoundaryCall) ordinal
                                           (operand: Fidelity.PSG.BoundaryOperand) =
        let (Fidelity.PSG.NodeId siteId) = call.Site
        let missing =
            $"Conditional optional-entry conversion at boundary call {siteId} operand {ordinal} requires source-authored assigned tag projection and both arm conversions."
        let stalePrefix =
            $"Conditional optional native-entry conversion at boundary call {siteId} operand {ordinal} has stale published source facts: "
        match operand.OptionalEntry with
        | Some (Fidelity.PSG.BoundaryOptionalEntryChoice.Conditional(selection, tagProjection, whenTrue, whenFalse)) ->
            match conditionalTagSelectionAt revision call operand selection tagProjection missing with
            | Ok selectedRow when
                whenTrue.Construction <> whenFalse.Construction
                && whenTrue.Obligation <> whenFalse.Obligation
                && Set.ofList [whenTrue.CaseOrdinal; whenFalse.CaseOrdinal] = Set.ofList [0; 1]
                && (selectedRow.Selection |> Option.exists (fun held ->
                    held.WhenTrue = whenTrue.Construction && held.WhenFalse = whenFalse.Construction)) ->
                let whenTrueIsSome = whenTrue.CaseOrdinal = 1
                let presentCandidate, absentCandidate =
                    if whenTrueIsSome then whenTrue, whenFalse
                    else whenFalse, whenTrue
                match optionalEntryPresentArmAt revision call ordinal operand presentCandidate missing,
                      optionalEntryAbsentArmAt revision call ordinal operand absentCandidate missing stalePrefix with
                | Ok presentArm, Ok absentArm ->
                    match Fidelity.PSG.Integrity.check revision with
                    | [] -> Ok(selection, tagProjection, selectedRow, whenTrueIsSome, presentArm, absentArm)
                    | violations -> Error (stalePrefix + Fidelity.PSG.Integrity.describe violations)
                | Error reason, _
                | _, Error reason -> Error reason
            | Error reason -> Error reason
            | Ok _ -> Error missing
        | _ -> Error missing

    /// Validate a current direct-call ReadOnlyBytes crossing against its
    /// published declaration, crossing mode, extent/termination claim, and retention claim.
    let readOnlyBufferUseAt (revision: Fidelity.PSG.Revision)
                            (call: Fidelity.PSG.BoundaryCall) ordinal
                            (operand: Fidelity.PSG.BoundaryOperand) =
        let (Fidelity.PSG.NodeId siteId) = call.Site
        let missing = $"Read-only buffer argument at boundary call {siteId} operand {ordinal} lacks its exact source crossing, extent/termination, or retention account."
        let boundary = revision.Emission.Boundary
        match operand.Abi with
        | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes declId ->
            match boundary.ReadOnlyBufferDeclarations.TryFind declId, boundary.Imports.TryFind call.Import with
            | Some roDecl, Some imported ->
                match boundary.ReadOnlyBufferUses.TryFind(call.Site, roDecl.Parameter) with
                | Some row when
                    operand.Adaptation.IsNone
                    && roDecl.Identity = declId
                    && imported.Binding = roDecl.Declaration
                    && imported.Identity = roDecl.Descriptor
                    && roDecl.Formals = (imported.Parameters |> List.map fst)
                    && roDecl.Formals |> List.tryItem ordinal = Some roDecl.BufferFormal
                    && row.Call = call.Site && row.Declaration = declId && row.Parameter = roDecl.Parameter
                    && row.Copies = 0 && row.Buffer = operand.Actual
                    && operand.Formal = roDecl.BufferFormal
                    && call.Entry.IsNone && call.Resource.IsNone
                    && not (boundary.WritableBufferUses.ContainsKey(call.Site, roDecl.Parameter)) ->
                    let crossingOk =
                        match row.Crossing, roDecl.Contract.Extent, roDecl.CountParameter, roDecl.CountFormal with
                        | Fidelity.PSG.BoundaryReadOnlyBufferCrossing.ExplicitZeroCopy(countParam, countNode, extentCapacity, extentCoverage),
                          BAREWire.Descriptors.ReadOnlyBufferExtent.ExplicitCount expectedParam, Some cp, Some countFormal
                            when expectedParam = countParam && cp = countParam ->
                            let countArgOk =
                                roDecl.Formals
                                |> List.tryFindIndex ((=) countFormal)
                                |> Option.bind (fun fi -> List.tryItem fi call.Arguments)
                                |> Option.exists (fun arg -> arg.Actual = countNode && arg.Formal = countFormal)
                            let extentOk =
                                match claimBodyAt revision extentCoverage "foreign-readonly-buffer-extent" with
                                | Some { Body = Fidelity.PSG.ObligationBody.ZeroCopyBufferExtent model } ->
                                    model.Call = call.Site && model.Declaration = declId && model.Parameter = roDecl.Parameter
                                    && model.CountParameter = countParam && model.Buffer = row.Buffer && model.Count = countNode
                                    && model.CountCoverage = extentCoverage && model.ExtentCapacity = extentCapacity
                                | _ -> false
                            countArgOk && extentOk
                        | Fidelity.PSG.BoundaryReadOnlyBufferCrossing.StaticImageNulBorrowed(poolEntry, staticOrigin, byteLength, terminationProof),
                          BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated, None, None ->
                            roDecl.Contract.Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                            && (match revision.StaticStringPool with
                                | Some pool ->
                                    match pool.Entries |> List.tryItem poolEntry with
                                    | Some entry -> List.contains staticOrigin entry.NodeIds
                                    | None -> false
                                | None -> false)
                            && (match claimBodyAt revision terminationProof "foreign-uncounted-path-termination" with
                                | Some { Body = Fidelity.PSG.ObligationBody.UncountedPathTermination model } ->
                                    model.Call = call.Site && model.Declaration = declId && model.Parameter = roDecl.Parameter
                                    && model.Source = row.Buffer && model.ByteLength = byteLength
                                    && model.Mode = Fidelity.PSG.UncountedPathStagingMode.StaticImageZeroCopy poolEntry
                                    && model.RequiresNoInteriorNul && model.RequiresTrailingNul
                                | _ -> false)
                        | Fidelity.PSG.BoundaryReadOnlyBufferCrossing.CallScopedNulStaged(stagingBuffer, capacity, byteLength, terminationProof),
                          BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated, None, None ->
                            roDecl.Contract.Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                            && stagingBuffer <> row.Buffer
                            && (match claimBodyAt revision terminationProof "foreign-uncounted-path-termination" with
                                | Some { Body = Fidelity.PSG.ObligationBody.UncountedPathTermination model } ->
                                    model.Call = call.Site && model.Declaration = declId && model.Parameter = roDecl.Parameter
                                    && model.Source = row.Buffer && model.ByteLength = byteLength
                                    && model.Mode = Fidelity.PSG.UncountedPathStagingMode.CallScopedStaged(stagingBuffer, capacity)
                                    && model.RequiresNoInteriorNul && model.RequiresTrailingNul
                                | _ -> false)
                        | _ -> false
                    let retentionOk =
                        match claimBodyAt revision row.RetentionProof "foreign-buffer-retention-domination" with
                        | Some { Body = Fidelity.PSG.ObligationBody.BufferRetentionDomination model } ->
                            let modeOk =
                                match roDecl.Contract.Retention, model.Mode with
                                | BAREWire.Descriptors.BufferRetention.DuringCall, Fidelity.PSG.BufferRetentionMode.DuringCall ->
                                    row.Retirements.IsEmpty && model.RetirementOrders.IsEmpty
                                | BAREWire.Descriptors.BufferRetention.RetainedUntil(owner, releases), Fidelity.PSG.BufferRetentionMode.RetainedUntilOwner(modelOwner, releaseCount) ->
                                    owner = modelOwner && releaseCount = Array.length releases
                                    && releaseCount > 0 && row.Retirements.Length = releaseCount
                                    && model.RetirementOrders.Length = releaseCount
                                | _ -> false
                            modeOk && model.Call = call.Site && model.Declaration = declId
                            && model.Buffer = row.Buffer && model.Residence = row.Residence
                        | _ -> false
                    if crossingOk && retentionOk then Ok(roDecl, row)
                    else Error missing
                | _ -> Error missing
            | _ -> Error missing
        | _ -> Error missing

    let private bufferAbsenceArmAt (revision: Fidelity.PSG.Revision)
                                   (call: Fidelity.PSG.BoundaryCall) ordinal
                                   (operand: Fidelity.PSG.BoundaryOperand)
                                   (selected: Fidelity.PSG.BoundaryBufferAbsenceSelection)
                                   missing =
        let boundary = revision.Emission.Boundary
        match operand.Abi with
        | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes declId
        | Fidelity.PSG.BoundaryScalar.WritableBytes declId when
            (selected.CaseOrdinal = 0 && selected.Payload.IsNone || selected.CaseOrdinal = 1 && selected.Payload.IsSome)
            && List.contains operand.Actual selected.Transport
            && List.contains selected.Construction selected.Transport ->
            match boundary.Imports.TryFind call.Import,
                  boundary.BufferAbsences.TryFind selected.Absence,
                  claimBodyAt revision selected.Obligation (sprintf "foreign-buffer-absence-conversion-%d" ordinal) with
            | Some imported, Some absence, Some { Body = Fidelity.PSG.ObligationBody.BufferAbsenceArgumentConversion model }
                when absence.Quote = selected.Absence && absence.Import = call.Import
                     && (imported.Parameters |> List.tryFindIndex (fun (f, _) -> f = absence.Formal) = Some ordinal)
                     && absence.Formal = operand.Formal
                     && absence.BufferDeclaration = declId
                     && model.Call = call.Site && model.Parameter = ordinal && model.Actual = operand.Actual
                     && model.Construction = selected.Construction && model.SourceCase = selected.CaseOrdinal
                     && model.Absence = selected.Absence
                     && model.Arms = [ { Fidelity.PSG.BufferAbsencePlanArm.CaseOrdinal = 0; Choice = Fidelity.PSG.BufferAbsencePlanChoice.AbsentNull }
                                       { Fidelity.PSG.BufferAbsencePlanArm.CaseOrdinal = 1; Choice = Fidelity.PSG.BufferAbsencePlanChoice.RequiresNonNullBuffer } ] ->
                let importedFormals = imported.Parameters |> List.map fst
                match operand.Abi with
                | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes roId ->
                    match boundary.ReadOnlyBufferDeclarations.TryFind roId with
                    | Some roDecl
                        when roDecl.Identity = roId
                             && roDecl.Descriptor = imported.Identity
                             && roDecl.Declaration = imported.Binding
                             && roDecl.Formals = importedFormals
                             && roDecl.BufferFormal = operand.Formal ->
                        if selected.CaseOrdinal = 0 then Ok selected
                        else readOnlyBufferUseAt revision call ordinal operand |> Result.map (fun _ -> selected)
                    | _ -> Error missing
                | Fidelity.PSG.BoundaryScalar.WritableBytes wbId ->
                    match boundary.WritableBufferDeclarations.TryFind wbId with
                    | Some wbDecl
                        when wbDecl.Identity = wbId
                             && wbDecl.Descriptor = imported.Identity
                             && wbDecl.Declaration = imported.Binding
                             && wbDecl.Formals = importedFormals
                             && wbDecl.BufferFormal = operand.Formal ->
                        if selected.CaseOrdinal = 0 then Ok selected
                        else
                            match boundary.WritableBufferUses.TryFind(call.Site, ordinal) with
                            | Some row when row.Call = call.Site && row.Declaration = wbId && row.Buffer = operand.Actual -> Ok selected
                            | _ -> Error missing
                    | _ -> Error missing
                | _ -> Error missing
            | _ -> Error missing
        | _ -> Error missing

    let bufferAbsenceConversionAt (revision: Fidelity.PSG.Revision)
                                  (call: Fidelity.PSG.BoundaryCall) ordinal
                                  (operand: Fidelity.PSG.BoundaryOperand) =
        let (Fidelity.PSG.NodeId siteId) = call.Site
        let missing = $"Optional byte-buffer absence conversion at boundary call {siteId} operand {ordinal} lacks its exact BufferAbsenceContract or claim."
        match operand.BufferAbsence with
        | Some (Fidelity.PSG.BoundaryBufferAbsenceChoice.Direct selected) ->
            bufferAbsenceArmAt revision call ordinal operand selected missing
        | _ -> Error missing

    let bufferAbsenceConditionalAt (revision: Fidelity.PSG.Revision)
                                   (call: Fidelity.PSG.BoundaryCall) ordinal
                                   (operand: Fidelity.PSG.BoundaryOperand) =
        let (Fidelity.PSG.NodeId siteId) = call.Site
        let missing = $"Conditional byte-buffer absence conversion at boundary call {siteId} operand {ordinal} requires source-authored assigned tag projection and both arm accounts."
        match operand.BufferAbsence with
        | Some (Fidelity.PSG.BoundaryBufferAbsenceChoice.Conditional(selection, tagProjection, whenTrue, whenFalse)) ->
            match conditionalTagSelectionAt revision call operand selection tagProjection missing with
            | Ok selectedRow when
                whenTrue.Construction <> whenFalse.Construction
                && whenTrue.Obligation <> whenFalse.Obligation
                && Set.ofList [whenTrue.CaseOrdinal; whenFalse.CaseOrdinal] = Set.ofList [0; 1]
                && (selectedRow.Selection |> Option.exists (fun held ->
                    held.WhenTrue = whenTrue.Construction && held.WhenFalse = whenFalse.Construction)) ->
                let whenTrueIsSome = whenTrue.CaseOrdinal = 1
                let presentCandidate, absentCandidate =
                    if whenTrueIsSome then whenTrue, whenFalse
                    else whenFalse, whenTrue
                match bufferAbsenceArmAt revision call ordinal operand presentCandidate missing,
                      bufferAbsenceArmAt revision call ordinal operand absentCandidate missing with
                | Ok presentArm, Ok absentArm -> Ok(selection, tagProjection, selectedRow, whenTrueIsSome, presentArm, absentArm)
                | Error reason, _
                | _, Error reason -> Error reason
            | Error reason -> Error reason
            | Ok _ -> Error missing
        | _ -> Error missing

    /// Validate a current BorrowedResultView return slice, invalidation frontier,
    /// optional companion call measurement, and scope claim.
    let borrowedResultViewAt (revision: Fidelity.PSG.Revision) (call: Fidelity.PSG.BoundaryCall) =
        let (Fidelity.PSG.NodeId siteId) = call.Site
        let missing = $"Borrowed result view at boundary call {siteId} lacks its exact non-owning declaration, invalidation frontier, or scope claim."
        let boundary = revision.Emission.Boundary
        match call.Result with
        | Some (Fidelity.PSG.BoundaryScalar.BorrowedBytes declId) ->
            match boundary.BorrowedResultViewDeclarations.TryFind declId,
                  boundary.BorrowedResultViewUses.TryFind call.Site,
                  boundary.Imports.TryFind call.Import with
            | Some bvDecl, Some bvUse, Some imported when
                call.ResultAdaptation.IsNone
                && bvDecl.Identity = declId
                && imported.Binding = bvDecl.Declaration && imported.Identity = bvDecl.Descriptor
                && bvDecl.Formals = (imported.Parameters |> List.map fst)
                && bvUse.Call = call.Site && bvUse.Declaration = declId && bvUse.View = call.Site
                && bvUse.NullToNoneBoundary
                && not bvUse.Invalidations.IsEmpty
                && bvUse.Invalidations.Length = bvUse.InvalidationOrders.Length
                && bvUse.Reads.Length = bvUse.ReadOrders.Length ->
                let ownerOk =
                    bvDecl.Formals
                    |> List.tryFindIndex ((=) bvDecl.OwnerFormal)
                    |> Option.bind (fun fi -> List.tryItem fi call.Arguments)
                    |> Option.exists (fun arg -> arg.Actual = bvUse.Owner && arg.Formal = bvDecl.OwnerFormal)
                let companionOk =
                    match bvDecl.Contract.Extent with
                    | BAREWire.Descriptors.BorrowedExtent.NulTerminated -> bvUse.CompanionCall.IsNone && bvUse.CompanionArguments.IsEmpty
                    | BAREWire.Descriptors.BorrowedExtent.CompanionCall(_, args) ->
                        match bvUse.CompanionCall |> Option.bind boundary.Calls.TryFind with
                        | Some compCall ->
                            compCall.Site <> call.Site
                            && compCall.Entry.IsNone
                            && compCall.Resource.IsNone
                            && compCall.Arguments.Length = Array.length args
                            && bvUse.CompanionArguments.Length = Array.length args
                            && (match boundary.Imports.TryFind compCall.Import with
                                | Some compImport ->
                                    compImport.Parameters = (compCall.Arguments |> List.map (fun actual -> actual.Formal, actual.Abi))
                                    && compCall.Result = compImport.Result
                                    && (match compImport.Result with Some(Fidelity.PSG.BoundaryScalar.Integer _) -> true | _ -> false)
                                | None -> false)
                            && (compCall.Arguments |> List.map (fun actual -> actual.Actual)) = bvUse.CompanionArguments
                        | None -> false
                let scopeOk =
                    match claimBodyAt revision bvUse.ScopeProof "foreign-borrowed-view-scope" with
                    | Some { Body = Fidelity.PSG.ObligationBody.BorrowedResultViewScope model } ->
                        model.Call = call.Site && model.Declaration = declId && model.Owner = bvUse.Owner
                        && model.View = bvUse.View && model.CallOrder = bvUse.CallOrder
                        && model.InvalidationOrders = bvUse.InvalidationOrders && model.ReadOrders = bvUse.ReadOrders
                        && model.NullToNoneBoundary
                    | _ -> false
                if ownerOk && companionOk && scopeOk then Ok(bvDecl, bvUse)
                else Error missing
            | _ -> Error missing
        | _ -> Error missing

    /// Read existing published lineage without classifying branch semantics or
    /// granting proof authority. Both the witness and target use these same rows.
    let resourceAccessAt (boundary: Fidelity.PSG.BoundaryEmissionProjection) site source kind =
        match boundary.ResourceAccesses.TryFind site with
        | Some access when access.Site = site && access.Source = source && access.Kind = kind ->
            match boundary.Calls.TryFind access.Acquisition with
            | Some acquisition ->
                match acquisition.Resource with
                | Some(Fidelity.PSG.BoundaryResourceUse.AcquireNullable resource) when
                    acquisition.Site = access.Acquisition
                    && resource.Declaration = access.Declaration
                    && resource.Cleanup = access.Cleanup ->
                    match boundary.ResourceDeclarations.TryFind access.Declaration with
                    | Some declaration when declaration.Identity = access.Declaration -> Ok(access, declaration)
                    | _ -> Error "Resource access has no exact current resource declaration."
                | _ -> Error "Resource access differs from its original acquisition and cleanup account."
            | None -> Error "Resource access has no current source-published acquisition."
        | _ -> Error "Resource access lacks its exact source-published site, subject and operation account."

    /// Signless MLIR types spell physical carriers; they do not replace source ABI facts.
    let scalarType = function
        | Fidelity.PSG.BoundaryScalar.Integer(bits, _) -> Ok (TInt(IntWidth bits))
        | Fidelity.PSG.BoundaryScalar.Boolean -> Ok (TInt(IntWidth 1))
        | Fidelity.PSG.BoundaryScalar.Entry _ -> Error "An entry carrier requires its source-published receiving signature."
        | Fidelity.PSG.BoundaryScalar.ResourceHandle _ ->
            Error "A resource carrier requires its exact direct-call conversion and cleanup accounts."
        | Fidelity.PSG.BoundaryScalar.WritableBytes _ ->
            Error "A writable byte carrier requires its exact source-published declaration."
        | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes _ ->
            Error "A read-only byte carrier requires its exact source-published declaration."
        | Fidelity.PSG.BoundaryScalar.BorrowedBytes _ ->
            Error "A borrowed result view carrier requires its exact source-published declaration."

    let rec private hasResourceCarrierSeen (boundary: Fidelity.PSG.BoundaryEmissionProjection) (seen: Set<Fidelity.PSG.NodeId>) = function
        | Fidelity.PSG.BoundaryScalar.ResourceHandle _ -> true
        | Fidelity.PSG.BoundaryScalar.Entry invocation when not (seen.Contains invocation) ->
            match boundary.CallbackInvocations.TryFind invocation with
            | Some row when row.Identity = invocation ->
                let nextSeen = seen.Add invocation
                (row.Signature.Parameters |> List.exists (hasResourceCarrierSeen boundary nextSeen))
                || (row.Signature.Result |> Option.exists (hasResourceCarrierSeen boundary nextSeen))
            | _ -> false
        | _ -> false

    let importCarriesResourceHandle (boundary: Fidelity.PSG.BoundaryEmissionProjection) (declaration: Fidelity.PSG.BoundaryImport) =
        (declaration.Parameters |> List.exists (snd >> hasResourceCarrierSeen boundary Set.empty))
        || (declaration.Result |> Option.exists (hasResourceCarrierSeen boundary Set.empty))

    let rec private trySignatureTypeWith (allowResource: bool) (boundary: Fidelity.PSG.BoundaryEmissionProjection) (seen: Set<Fidelity.PSG.NodeId>) (invocation: Fidelity.PSG.NodeId) (signature: Fidelity.PSG.NativeEntrySignature) : Result<MLIRType option, string> =
        if signature.CallingConvention <> "CDecl" then
            Error "A closed native entry requires its source-published CDecl convention."
        else
            let rec collectParams ordinal acc = function
                | [] -> Ok (List.rev acc)
                | scalar :: rest ->
                    match tryScalarTypeContextWith allowResource boundary seen (Some(invocation, ordinal)) scalar with
                    | Ok tyOpt -> collectParams (ordinal + 1) (tyOpt :: acc) rest
                    | Error reason -> Error reason
            match collectParams 0 [] signature.Parameters, signature.Result with
            | Error reason, _ -> Error reason
            | Ok paramOpts, None ->
                if List.exists Option.isNone paramOpts then Ok None
                else Ok (Some (TFunc(List.choose id paramOpts, [])))
            | Ok paramOpts, Some retScalar ->
                tryScalarTypeContextWith allowResource boundary seen None retScalar
                |> Result.map (fun retOpt ->
                    match retOpt with
                    | Some retTy when not (List.exists Option.isNone paramOpts) ->
                        Some (TFunc(List.choose id paramOpts, [retTy]))
                    | _ -> None)

    and private tryScalarTypeContextWith (allowResource: bool) (boundary: Fidelity.PSG.BoundaryEmissionProjection) (seen: Set<Fidelity.PSG.NodeId>) (callbackContext: (Fidelity.PSG.NodeId * int) option) = function
        | Fidelity.PSG.BoundaryScalar.Integer(bits, _) -> Ok (Some (TInt(IntWidth bits)))
        | Fidelity.PSG.BoundaryScalar.Boolean -> Ok (Some (TInt(IntWidth 1)))
        | Fidelity.PSG.BoundaryScalar.Entry invocation when seen.Contains invocation ->
            Error "An entry carrier contains a recursive receiving invocation."
        | Fidelity.PSG.BoundaryScalar.Entry invocation ->
            match boundary.CallbackInvocations.TryFind invocation with
            | Some row when row.Identity = invocation -> trySignatureTypeWith allowResource boundary (seen.Add invocation) invocation row.Signature
            | _ -> Error "An entry carrier lacks its exact source-published receiving invocation."
        | Fidelity.PSG.BoundaryScalar.ResourceHandle _ ->
            if allowResource then Ok None
            else Error "A resource carrier requires its exact direct-call conversion and cleanup accounts."
        | Fidelity.PSG.BoundaryScalar.WritableBytes identity ->
            match boundary.WritableBufferDeclarations.TryFind identity with
            | Some row when row.Identity = identity -> Ok (Some (TMemRef(TInt(IntWidth 8))))
            | _ -> Error "A writable byte carrier lacks its exact source-published declaration."
        | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes identity ->
            match callbackContext with
            | Some(invocation, ordinal) ->
                match boundary.CountedEntryArrays.TryFind identity with
                | Some counted when counted.Identity = identity && counted.Invocation = invocation && counted.Contract.Argument = ordinal ->
                    Ok (Some (TMemRef(TInt(IntWidth 8))))
                | _ -> Error "A callback counted-entry array lacks its exact receiving invocation or parameter ordinal."
            | None ->
                match boundary.ReadOnlyBufferDeclarations.TryFind identity with
                | Some row when row.Identity = identity -> Ok (Some (TMemRef(TInt(IntWidth 8))))
                | _ -> Error "A read-only byte carrier lacks its exact source-published declaration."
        | Fidelity.PSG.BoundaryScalar.BorrowedBytes identity ->
            match boundary.BorrowedResultViewDeclarations.TryFind identity with
            | Some row when row.Identity = identity -> Ok (Some (TMemRef(TInt(IntWidth 8))))
            | _ -> Error "A borrowed result view carrier lacks its exact source-published declaration."

    let tryScalarTypeIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) (seen: Set<Fidelity.PSG.NodeId>) scalar =
        match tryScalarTypeContextWith false boundary seen None scalar with
        | Ok (Some ty) -> Ok ty
        | Ok None -> Error "A resource carrier requires its exact direct-call conversion and cleanup accounts."
        | Error reason -> Error reason

    let private tryHandleTypeFromRepresentation (nullable: bool) (expectedHandleType: Fidelity.PSG.TypeIdentity option) (expectedBits: int option) (rep: Fidelity.PSG.ValueRepresentation) =
        if not (matchesCHandleRepresentation nullable expectedHandleType expectedBits rep) then None
        elif not nullable then
            match rep with
            | Fidelity.PSG.ValueRepresentation.Scalar slot -> SettledScalar.tryType slot
            | _ -> None
        else Some (TResourceOption rep)

    /// Validate a published CDecl callback invocation and derive its closed native
    /// function signature fail-closed from settled PSG and boundary facts.
    let tryCallbackSignatureTypeAt (revision: Fidelity.PSG.Revision) (invocation: Fidelity.PSG.NodeId) : Result<MLIRType, string> =
        let boundary = revision.Emission.Boundary
        match boundary.CallbackInvocations.TryFind invocation with
        | Some row when row.Identity = invocation ->
            if row.Signature.CallingConvention <> "CDecl" then
                Error "A closed native entry requires its source-published CDecl convention."
            else
                match boundary.Imports.TryFind row.Import with
                | Some callbackImp ->
                    let seen = Set.singleton invocation
                    let settledResourceRep (res: Fidelity.PSG.BoundaryResourceDeclaration) ordinal nullable =
                        let fromCallback = callbackHandleRepAt revision callbackImp row.Formal ordinal nullable
                        let fromDeclType =
                            if nullable then None
                            else settledRepresentationForTypeAndNode revision (Some res.Identity) res.HandleType
                        match fromCallback, fromDeclType with
                        | Some r1, Some r2 -> if r1 = r2 then Some r1 else None
                        | Some r1, None -> Some r1
                        | None, Some r2 -> Some r2
                        | None, None -> None
                    let checkParam ordinal = function
                        | Fidelity.PSG.BoundaryScalar.ResourceHandle(decl, nullable) ->
                            if boundary.ResourceDeclarations.ContainsKey decl then
                                match boundary.ResourceDeclarations.TryFind decl with
                                | Some res when res.Identity = decl && res.PointerBits > 0 ->
                                    match settledResourceRep res ordinal nullable
                                          |> Option.bind (tryHandleTypeFromRepresentation nullable (Some res.HandleType) (Some res.PointerBits)) with
                                    | Some ty -> Ok ty
                                    | None -> Error "A callback resource parameter lacks its exact source-settled handle representation."
                                | _ ->
                                    Error "A callback resource parameter lacks its exact resource declaration."
                            elif decl <> row.Formal then
                                Error "A callback borrowed handle parameter disagrees with its callback formal identity."
                            else
                                match callbackHandleRepAt revision callbackImp row.Formal ordinal nullable
                                      |> Option.bind (tryHandleTypeFromRepresentation nullable None None) with
                                | Some ty -> Ok ty
                                | None -> Error "A callback borrowed handle parameter lacks its exact source-settled handle representation."
                        | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes decl ->
                            match boundary.CountedEntryArrays.TryFind decl with
                            | Some counted when counted.Identity = decl && counted.Invocation = row.Identity && counted.Contract.Argument = ordinal ->
                                Ok (TMemRef(TInt(IntWidth 8)))
                            | _ -> Error "A callback counted-entry array lacks its exact receiving invocation or parameter ordinal."
                        | scalar ->
                            tryScalarTypeIn boundary seen scalar
                    let rec collectParams ordinal acc = function
                        | [] -> Ok (List.rev acc)
                        | scalar :: rest ->
                            match checkParam ordinal scalar with
                            | Ok ty -> collectParams (ordinal + 1) (ty :: acc) rest
                            | Error reason -> Error reason
                    let resultTypesResult =
                        match row.Signature.Result with
                        | None -> Ok []
                        | Some (Fidelity.PSG.BoundaryScalar.ResourceHandle _) ->
                            Error "A callback signature cannot return a resource handle."
                        | Some scalar ->
                            tryScalarTypeIn boundary seen scalar |> Result.map List.singleton
                    match collectParams 0 [] row.Signature.Parameters, resultTypesResult with
                    | Ok paramTypes, Ok resultTypes -> Ok (TFunc(paramTypes, resultTypes))
                    | Error reason, _ -> Error reason
                    | _, Error reason -> Error reason
                | None -> Error "A callback entry carrier lacks its exact receiving import."
        | _ -> Error "A callback entry carrier lacks its exact receiving invocation."

    /// Validate settled BorrowedBytes or Option<BorrowedBytes> view representations
    /// without hardcoding byte widths or synthesizing pointer placement.
    let matchesBorrowedResultViewRepresentation (rep: Fidelity.PSG.ValueRepresentation) =
        let isByteBuffer = function
            | Fidelity.PSG.ValueRepresentation.Buffer(None, Fidelity.PSG.ValueRepresentation.Scalar(Fidelity.PSG.SettledSlot.Integer(8, _))) -> true
            | Fidelity.PSG.ValueRepresentation.Buffer(Some bytes, Fidelity.PSG.ValueRepresentation.Scalar(Fidelity.PSG.SettledSlot.Integer(8, _))) -> bytes > 0
            | _ -> false
        if isByteBuffer rep then true
        else
            match rep with
            | Fidelity.PSG.ValueRepresentation.Union(cases, Some(_, bytes, optAlign))
                when cases.Length = 2 && bytes > 0 && optAlign > 0 ->
                (cases |> List.filter (snd >> List.isEmpty) |> List.length) = 1
                && (cases |> List.filter (fun (_, payloads) ->
                    match payloads with
                    | [p] -> isByteBuffer p
                    | _ -> false) |> List.length) = 1
            | _ -> false

    /// Validate a BorrowedBytes call result node against its published
    /// OccurrenceRepresentations entry and computed MLIRType.
    let matchesBorrowedResultViewAt (revision: Fidelity.PSG.Revision) (site: Fidelity.PSG.NodeId) (nodeType: MLIRType) =
        match revision.Emission.Numeric.OccurrenceRepresentations.TryFind site with
        | Some (Ok rep) when matchesBorrowedResultViewRepresentation rep ->
            match nodeType with
            | TMemRef(TInt(IntWidth 8)) ->
                match rep with
                | Fidelity.PSG.ValueRepresentation.Buffer(None, Fidelity.PSG.ValueRepresentation.Scalar(Fidelity.PSG.SettledSlot.Integer(8, _))) -> true
                | _ -> false
            | TMemRefStatic(bytes, TInt(IntWidth 8)) ->
                match rep with
                | Fidelity.PSG.ValueRepresentation.Buffer(Some repBytes, Fidelity.PSG.ValueRepresentation.Scalar(Fidelity.PSG.SettledSlot.Integer(8, _))) ->
                    bytes > 0 && bytes = repBytes
                | Fidelity.PSG.ValueRepresentation.Union(_, Some(_, repBytes, _)) ->
                    bytes > 0 && bytes = repBytes
                | _ -> false
            | _ -> false
        | _ -> false

    let validateImportCarriersIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) (declaration: Fidelity.PSG.BoundaryImport) : Result<unit, string> =
        let rec checkParams = function
            | [] -> Ok ()
            | (_, scalar) :: rest ->
                match tryScalarTypeContextWith true boundary Set.empty None scalar with
                | Ok _ -> checkParams rest
                | Error reason -> Error reason
        checkParams declaration.Parameters
        |> Result.bind (fun () ->
            match declaration.Result with
            | None -> Ok ()
            | Some ret -> tryScalarTypeContextWith true boundary Set.empty None ret |> Result.map ignore)

    let rec signatureTypeIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) (signature: Fidelity.PSG.NativeEntrySignature) : Result<MLIRType, string> =
        if signature.CallingConvention <> "CDecl" then
            Error "A closed native entry requires its source-published CDecl convention."
        else
            let rec collectParams acc = function
                | [] -> Ok (List.rev acc)
                | s :: rest ->
                    match scalarTypeIn boundary s with
                    | Ok ty -> collectParams (ty :: acc) rest
                    | Error reason -> Error reason
            let resultTypes =
                match signature.Result with
                | None -> Ok []
                | Some s -> scalarTypeIn boundary s |> Result.map List.singleton
            match collectParams [] signature.Parameters, resultTypes with
            | Ok paramTypes, Ok retTypes -> Ok (TFunc(paramTypes, retTypes))
            | Error reason, _ | _, Error reason -> Error reason

    and signatureType (signature: Fidelity.PSG.NativeEntrySignature) : Result<MLIRType, string> =
        if signature.CallingConvention <> "CDecl" then
            Error "A closed native entry requires its source-published CDecl convention."
        else
            let rec collectParams acc = function
                | [] -> Ok (List.rev acc)
                | s :: rest ->
                    match scalarType s with
                    | Ok ty -> collectParams (ty :: acc) rest
                    | Error reason -> Error reason
            let resultTypes =
                match signature.Result with
                | None -> Ok []
                | Some s -> scalarType s |> Result.map List.singleton
            match collectParams [] signature.Parameters, resultTypes with
            | Ok paramTypes, Ok retTypes -> Ok (TFunc(paramTypes, retTypes))
            | Error reason, _ | _, Error reason -> Error reason

    and scalarTypeIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) scalar : Result<MLIRType, string> =
        tryScalarTypeIn boundary Set.empty scalar

    let tryParametersIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        let rec collect acc = function
            | [] -> Ok (List.rev acc)
            | (_, scalar) :: rest ->
                match tryScalarTypeIn boundary Set.empty scalar with
                | Ok ty -> collect (ty :: acc) rest
                | Error reason -> Error reason
        collect [] declaration.Parameters

    let parametersIn boundary (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        tryParametersIn boundary declaration

    let resultsIn boundary (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        match declaration.Result with
        | None -> Ok []
        | Some scalar -> scalarTypeIn boundary scalar |> Result.map List.singleton

    let parameters (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        let rec collect acc = function
            | [] -> Ok (List.rev acc)
            | (_, scalar) :: rest ->
                match scalarType scalar with
                | Ok ty -> collect (ty :: acc) rest
                | Error reason -> Error reason
        collect [] declaration.Parameters

    let results (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        match declaration.Result with
        | None -> Ok []
        | Some scalar -> scalarType scalar |> Result.map List.singleton

    let rec private tryRepresentationStructType = function
        | Fidelity.PSG.ValueRepresentation.Scalar slot -> SettledScalar.tryType slot
        | Fidelity.PSG.ValueRepresentation.Record(fields, Some(offsets, size, alignment))
            when size > 0 && alignment > 0 && offsets.Length = fields.Length ->
            let rec collect acc = function
                | [] -> Some(TStruct(List.rev acc, Some { Offsets = offsets; Size = size; Align = alignment }))
                | (name, rep) :: rest ->
                    match tryRepresentationStructType rep with
                    | Some ty -> collect ((name, ty) :: acc) rest
                    | None -> None
            collect [] fields
        | _ -> None

    /// Extract the final return TypeIdentity of a curried or uncurried function TypeIdentity.
    let rec private returnTypeOfSignature = function
        | Fidelity.PSG.TypeIdentity.Function(_, range) -> returnTypeOfSignature range
        | other -> other

    /// Check whether a settled Record layout and nominal TypeIdentity match a published shared-buffer StructDescriptor.
    let private placementMatchesType
        (typeId: Fidelity.PSG.TypeIdentity)
        (layoutFields: Fidelity.PSG.SettledField list)
        (lSize: int)
        (lAlign: int)
        (pl: Fidelity.PSG.BoundarySharedBufferPlacementDeclaration)
        : bool =
        let st = pl.Placement.StructLayout
        let nominalMatches =
            match typeId with
            | Fidelity.PSG.TypeIdentity.Application(tc, []) when tc.NativeKind.IsNone ->
                let qualTypeName =
                    match tc.Declaration.Module with
                    | [] -> tc.Declaration.Name
                    | mods -> String.concat "." mods + "." + tc.Declaration.Name
                if String.exists ((=) '.') st.Name then
                    qualTypeName = st.Name
                else
                    tc.Declaration.Name = st.Name
            | _ -> false
        let stFields = Array.toList st.Layout.Fields
        nominalMatches
        && st.Layout.Size = lSize
        && st.Layout.Alignment = lAlign
        && stFields.Length = layoutFields.Length
        && (List.zip layoutFields stFields
            |> List.forall (fun (sf, df) ->
                sf.Name = df.Name
                && sf.Offset = Some df.Offset
                && sf.Size.IsSome
                && sf.Align.IsSome))

    /// Check whether `typeId` is a settled shared-buffer Record layout matching `pl`.
    let private typeMatchesPlacement
        (revision: Fidelity.PSG.Revision)
        (typeId: Fidelity.PSG.TypeIdentity)
        (pl: Fidelity.PSG.BoundarySharedBufferPlacementDeclaration)
        : bool =
        revision.Emission.Numeric.Layouts
        |> Map.exists (fun k layout ->
            k = typeId
            && (match layout with
                | Fidelity.PSG.SettledLayout.Record(fields, Some sz, Some al) ->
                    placementMatchesType typeId fields sz al pl
                | _ -> false))

    /// Check whether `imp` matches a qualified Clef binding name (`Module.funcName`) in `pl.RegionDescriptor`.
    /// Note: `AXA006` (`tools/Alex.Analyzers/Analyzer.fs:1640`) forbids payload extraction from
    /// `BoundaryImport.DeclarationFacts` in `src/Alex` (permitting only `ContainsKey` / `Map.containsKey`);
    /// `Fidelity.PSG.Integrity.check` validates `imp.DeclarationFacts[imp.Binding]` (`Form = "binding"`),
    /// while `Alex` resolves the qualified binding name strictly from `SourceReadings.ContextHeaders`
    /// and `Emission.Callable.Symbols` (`CallableSymbolName.ModuleBinding`).
    let private importMatchesRegionBinding
        (revision: Fidelity.PSG.Revision)
        (imp: Fidelity.PSG.BoundaryImport)
        (expectedQualName: string)
        : bool =
        if Alex.Text.isBlank expectedQualName || not (imp.DeclarationFacts.ContainsKey imp.Binding) then
            false
        else
            let moduleNames =
                revision.SourceReadings.ContextHeaders
                |> Map.toList
                |> List.choose (fun (hid, header) ->
                    if hid = imp.Scope && not (Alex.Text.isBlank header.Name) then
                        Some header.Name
                    else
                        None)
            let declBindingNames =
                revision.Emission.Callable.Symbols
                |> Map.toList
                |> List.choose (fun (bid, sym) ->
                    if bid = imp.Binding then
                        match sym with
                        | Fidelity.PSG.CallableSymbolName.ModuleBinding(modName, bindName)
                            when not (Alex.Text.isBlank modName) && not (Alex.Text.isBlank bindName) ->
                            Some (modName, bindName)
                        | _ -> None
                    else
                        None)
            match moduleNames, declBindingNames with
            | [ modName ], [ (symModName, bindName) ] when modName = symModName ->
                (modName + "." + bindName) = expectedQualName
            | _ -> false

    /// Check whether `imp` matches one of the consumer roles (Release, Sync, or ForeignUses) in `pl.RegionDescriptor`.
    let private importMatchesConsumerRole
        (revision: Fidelity.PSG.Revision)
        (imp: Fidelity.PSG.BoundaryImport)
        (pl: Fidelity.PSG.BoundarySharedBufferPlacementDeclaration)
        : bool =
        let rd = pl.RegionDescriptor
        (match rd.Release with
         | Some r -> importMatchesRegionBinding revision imp r
         | None -> false)
        || (rd.Sync |> Array.exists (importMatchesRegionBinding revision imp))
        || (rd.ForeignUses |> Array.exists (importMatchesRegionBinding revision imp))

    /// Validate all published shared-buffer placement and view-use rows in the revision.
    let sharedBufferIntegrityIn (revision: Fidelity.PSG.Revision) : Result<unit, string> =
        let sharedViolations =
            Fidelity.PSG.Integrity.check revision
            |> List.filter (fun v ->
                Alex.Text.startsWith "Emission.Boundary.SharedBufferPlacements" v.Part
                || Alex.Text.startsWith "Emission.Boundary.SharedBufferViewUses" v.Part)
        let boundary = revision.Emission.Boundary
        let placementRows = Map.toList boundary.SharedBufferPlacements
        let viewUseRows = Map.toList boundary.SharedBufferViewUses
        let claimMatchesPlacement
            (pl: Fidelity.PSG.BoundarySharedBufferPlacementDeclaration)
            (cid: Fidelity.PSG.NodeId, expectedFormKind: string)
            : bool =
            List.contains cid pl.Obligations
            && (revision.CurrentClaims
                |> Map.exists (fun k info ->
                    k = cid
                    && List.contains info revision.Obligations
                    && (match info.Body with
                        | Fidelity.PSG.ObligationBody.SharedBufferPlacementObligation ob ->
                            let suffix = ":" + pl.Placement.Name
                            let sourceMatchesPlacement =
                                ob.Source = pl.Placement.Name
                                || (String.length ob.Source >= String.length suffix
                                    && Seq.forall2 (=) suffix (Seq.skip (String.length ob.Source - String.length suffix) ob.Source))
                            let matchesPlacement =
                                if expectedFormKind = BAREWire.Platform.FormKind.SharedBufferSpaceExtent then
                                    ob.Form.A = pl.Space.Capacity
                                    && Array.contains pl.Placement.Name ob.Form.Names
                                elif expectedFormKind = BAREWire.Platform.FormKind.SharedBufferLayout
                                     || expectedFormKind = BAREWire.Platform.FormKind.SharedBufferExclusivity then
                                    sourceMatchesPlacement
                                    && ob.Form.A = int64 (Array.length pl.Placement.StructLayout.Layout.Fields)
                                elif expectedFormKind = BAREWire.Platform.FormKind.SharedBufferExtent then
                                    sourceMatchesPlacement
                                    && ob.Form.A = int64 pl.Placement.MeasuredElementSize
                                elif expectedFormKind = BAREWire.Platform.FormKind.SharedBufferLifetime then
                                    sourceMatchesPlacement
                                    && ob.Form.A = 0L
                                else
                                    false
                            info.Id = ob.Id
                            && info.Kind = ob.Kind
                            && info.Logic = ob.Logic
                            && ob.Form.Kind = expectedFormKind
                            && matchesPlacement
                        | _ -> false)))
        let expectedPlacementForms =
            [ BAREWire.Platform.FormKind.SharedBufferLayout
              BAREWire.Platform.FormKind.SharedBufferExtent
              BAREWire.Platform.FormKind.SharedBufferSpaceExtent
              BAREWire.Platform.FormKind.SharedBufferLifetime
              BAREWire.Platform.FormKind.SharedBufferExclusivity ]
        let rec checkPlacements = function
            | [] -> Ok ()
            | (Fidelity.PSG.NodeId plId, (pl: Fidelity.PSG.BoundarySharedBufferPlacementDeclaration)) :: rest ->
                let distinctPlObs = List.distinct pl.Obligations
                let allFormsPresent =
                    expectedPlacementForms
                    |> List.forall (fun fk ->
                        pl.Obligations |> List.exists (fun cid -> claimMatchesPlacement pl (cid, fk)))
                if distinctPlObs.Length <> 5 || pl.Obligations.Length <> 5 || not allFormsPresent then
                    Error (sprintf "Shared-buffer placement %d lacks valid shared-buffer obligations in CurrentClaims." plId)
                else
                    checkPlacements rest
        let callMatchesRole (callId: Fidelity.PSG.NodeId) (expectedBindings: string list) =
            boundary.Calls
            |> Map.exists (fun cid call ->
                cid = callId
                && call.Site = callId
                && (boundary.Imports
                    |> Map.exists (fun impId imp ->
                        impId = call.Import
                        && (expectedBindings |> List.exists (importMatchesRegionBinding revision imp)))))
        let rec checkCrossRowExclusivity seenCalls seenProjs = function
            | [] -> Ok ()
            | (Fidelity.PSG.NodeId siteId, (vu: Fidelity.PSG.BoundarySharedBufferViewUse)) :: rest ->
                let rowCalls =
                    (vu.RegionAcquisitionCall :: Option.toList vu.RegionReleaseCall)
                    @ vu.SyncCalls
                    @ vu.ForeignUseCalls
                let rowProjs = vu.ViewProjections @ vu.WriteProjections
                if rowCalls |> List.exists (fun c -> Set.contains c seenCalls) then
                    Error (sprintf "Shared-buffer view use %d shares a role call site with another view use." siteId)
                elif rowProjs |> List.exists (fun p -> Set.contains p seenProjs) then
                    Error (sprintf "Shared-buffer view use %d shares a projection site with another view use." siteId)
                else
                    checkCrossRowExclusivity
                        (Set.union seenCalls (Set.ofList rowCalls))
                        (Set.union seenProjs (Set.ofList rowProjs))
                        rest
        let rec checkViewUses = function
            | [] ->
                match checkCrossRowExclusivity Set.empty Set.empty viewUseRows with
                | Error err -> Error err
                | Ok () ->
                    match sharedViolations with
                    | [] -> Ok ()
                    | violations -> Error (Fidelity.PSG.Integrity.describe violations)
            | (key, (vu: Fidelity.PSG.BoundarySharedBufferViewUse)) :: rest ->
                let (Fidelity.PSG.NodeId siteId) = key
                if vu.Copies <> 0 then
                    Error (sprintf "Shared-buffer view use %d has non-zero Copies = %d." siteId vu.Copies)
                else
                    match boundary.SharedBufferPlacements.TryFind vu.PlacementDeclaration with
                    | None ->
                        Error (sprintf "Shared-buffer view use %d references missing placement declaration." siteId)
                    | Some pl ->
                        let isReadOnly =
                            pl.Placement.SpaceDescriptor.Access = "ReadOnly"
                            || pl.Placement.ViewLayout.Access = BAREWire.Hardware.AccessKind.ReadOnly
                            || pl.Space.Access = BAREWire.Platform.Access.ReadOnly
                        let isWriteOnly =
                            pl.Placement.SpaceDescriptor.Access = "WriteOnly"
                            || pl.Placement.ViewLayout.Access = BAREWire.Hardware.AccessKind.WriteOnly
                            || pl.Space.Access = BAREWire.Platform.Access.WriteOnly
                        if isReadOnly && not vu.WriteProjections.IsEmpty then
                            Error (sprintf "Shared-buffer view use %d has write projections on a ReadOnly placement." siteId)
                        elif isWriteOnly && not vu.ViewProjections.IsEmpty then
                            Error (sprintf "Shared-buffer view use %d has read projections on a WriteOnly placement." siteId)
                        else
                            let vuObIds =
                                [ vu.LayoutObligation, BAREWire.Platform.FormKind.SharedBufferLayout
                                  vu.ExtentObligation, BAREWire.Platform.FormKind.SharedBufferExtent
                                  vu.SpaceExtentObligation, BAREWire.Platform.FormKind.SharedBufferSpaceExtent
                                  vu.LifetimeObligation, BAREWire.Platform.FormKind.SharedBufferLifetime
                                  vu.ExclusivityObligation, BAREWire.Platform.FormKind.SharedBufferExclusivity ]
                            let distinctObIds = vuObIds |> List.map fst |> List.distinct
                            if distinctObIds.Length <> 5 || pl.Obligations.Length <> 5 || not (vuObIds |> List.forall (claimMatchesPlacement pl)) then
                                Error (sprintf "Shared-buffer view use %d lacks valid shared-buffer obligations in CurrentClaims." siteId)
                            else
                                let roleCallsMatchDescriptor =
                                    callMatchesRole vu.RegionAcquisitionCall [ pl.RegionDescriptor.Acquire ]
                                    && (match vu.RegionReleaseCall, pl.RegionDescriptor.Release with
                                        | None, _ -> true
                                        | Some relCall, Some relName -> callMatchesRole relCall [ relName ]
                                        | Some _, None -> false)
                                    && (vu.SyncCalls |> List.forall (fun sc -> callMatchesRole sc (Array.toList pl.RegionDescriptor.Sync)))
                                    && (vu.ForeignUseCalls |> List.forall (fun fc -> callMatchesRole fc (Array.toList pl.RegionDescriptor.ForeignUses)))
                                if not roleCallsMatchDescriptor then
                                    Error (sprintf "Shared-buffer view use %d role call does not match its placement RegionDescriptor." siteId)
                                else
                                    let allUseOrders =
                                        vu.SyncOrders @ vu.ForeignUseOrders @ vu.ProjectionOrders @ vu.WriteProjectionOrders
                                    let allOrders =
                                        vu.AcquisitionOrder :: (Option.toList vu.ReleaseOrder @ allUseOrders)
                                    let syncDisjointFromForeign =
                                        vu.SyncCalls |> List.forall (fun sc -> not (List.contains sc vu.ForeignUseCalls))
                                    let releaseScheduleOk =
                                        if not pl.Placement.LeakedAtExit then
                                            match vu.RegionReleaseCall, vu.ReleaseOrder with
                                            | Some _, Some relOrd ->
                                                vu.AcquisitionOrder >= 0
                                                && vu.AcquisitionOrder < relOrd
                                                && (allUseOrders |> List.forall (fun ord -> vu.AcquisitionOrder < ord && ord < relOrd))
                                            | _ -> false
                                        else
                                            vu.RegionReleaseCall.IsNone
                                            && vu.ReleaseOrder.IsNone
                                            && not allUseOrders.IsEmpty
                                            && vu.AcquisitionOrder >= 0
                                            && (allUseOrders |> List.forall (fun ord -> vu.AcquisitionOrder < ord))
                                    let ordersOk =
                                        releaseScheduleOk
                                        && (List.distinct allOrders).Length = allOrders.Length
                                        && syncDisjointFromForeign
                                        && vu.ViewProjections.Length = vu.ProjectionOrders.Length
                                        && vu.WriteProjections.Length = vu.WriteProjectionOrders.Length
                                        && vu.SyncCalls.Length = vu.SyncOrders.Length
                                        && vu.ForeignUseCalls.Length = vu.ForeignUseOrders.Length
                                    if not ordersOk then
                                        Error (sprintf "Shared-buffer view use %d violates acquisition/projection/release order domination." siteId)
                                    else
                                        let clefOrders = vu.ProjectionOrders @ vu.WriteProjectionOrders
                                        let syncBracketOk =
                                            if vu.ForeignUseOrders.IsEmpty || clefOrders.IsEmpty || isReadOnly then
                                                true
                                            else
                                                not vu.SyncOrders.IsEmpty
                                                && (vu.ForeignUseOrders |> List.forall (fun fOrd ->
                                                    clefOrders |> List.forall (fun pOrd ->
                                                        vu.SyncOrders |> List.exists (fun sOrd ->
                                                            (fOrd < sOrd && sOrd < pOrd) || (pOrd < sOrd && sOrd < fOrd)))))
                                        if not syncBracketOk then
                                            Error (sprintf "Shared-buffer view use %d has unbracketed foreign use call without dominating sync." siteId)
                                        else
                                            checkViewUses rest
        match checkPlacements placementRows with
        | Error err -> Error err
        | Ok () -> checkViewUses viewUseRows

    /// Resolve a settled shared-buffer StructDescriptor record type to its TStruct carrier.
    let sharedBufferStructTypeAt (revision: Fidelity.PSG.Revision) (typeId: Fidelity.PSG.TypeIdentity) : Result<MLIRType, string> =
        let boundary = revision.Emission.Boundary
        let numeric = revision.Emission.Numeric
        match numeric.Layouts.TryFind typeId with
        | Some(Fidelity.PSG.SettledLayout.Record(layoutFields, Some lSize, Some lAlign)) ->
            let matchingPlacements =
                boundary.SharedBufferPlacements.Values
                |> Seq.filter (placementMatchesType typeId layoutFields lSize lAlign)
                |> Seq.toList
            let viewUsePlacementsOk =
                boundary.SharedBufferViewUses.Values
                |> Seq.filter (fun vu -> vu.ElementType = typeId)
                |> Seq.forall (fun vu ->
                    boundary.SharedBufferPlacements
                    |> Map.exists (fun k pl ->
                        k = vu.PlacementDeclaration
                        && placementMatchesType typeId layoutFields lSize lAlign pl))
            if matchingPlacements.IsEmpty || not viewUsePlacementsOk then
                Error "Type is not a published shared-buffer StructDescriptor type."
            else
                match numeric.TypeRepresentations.TryFind typeId with
                | Some(Ok rep) ->
                    match tryRepresentationStructType rep with
                    | Some(TStruct(fields, Some bytes) as structTy) ->
                        let fieldsMatch =
                            fields.Length = layoutFields.Length
                            && bytes.Offsets.Length = layoutFields.Length
                            && (List.zip3 fields bytes.Offsets layoutFields
                                |> List.forall (fun ((fName, _), fOff, sf) -> fName = sf.Name && Some fOff = sf.Offset))
                        if bytes.Size = lSize && bytes.Align = lAlign && fieldsMatch then
                            Ok structTy
                        else
                            Error "Shared-buffer type representation disagrees with its settled Record layout."
                    | _ -> Error "Shared-buffer type representation is not a settled TStruct."
                | _ -> Error "Shared-buffer type lacks its settled TypeRepresentation."
        | _ -> Error "Shared-buffer type lacks its settled Record layout."

    let isSharedBufferStructType (revision: Fidelity.PSG.Revision) (typeId: Fidelity.PSG.TypeIdentity) : bool =
        match sharedBufferStructTypeAt revision typeId with
        | Ok _ -> true
        | Error _ -> false

    /// Find placements for which `imp` is a consumer role import (Release, Sync, or ForeignUses).
    let private placementsForConsumerImport (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) : Fidelity.PSG.BoundarySharedBufferPlacementDeclaration list =
        let boundary = revision.Emission.Boundary
        let callingViewUses =
            boundary.SharedBufferViewUses.Values
            |> Seq.filter (fun vu ->
                (Option.toList vu.RegionReleaseCall @ vu.SyncCalls @ vu.ForeignUseCalls)
                |> List.exists (fun callId ->
                    boundary.Calls
                    |> Map.exists (fun cid c -> cid = callId && c.Import = imp.Identity)))
            |> Seq.toList
        let namedByAnyViewUse = not callingViewUses.IsEmpty
        let fromViewUses =
            let matchedPerView =
                callingViewUses
                |> List.map (fun vu ->
                    boundary.SharedBufferPlacements
                    |> Map.toList
                    |> List.choose (fun (pid, pl) ->
                        if pid = vu.PlacementDeclaration && importMatchesConsumerRole revision imp pl then
                            Some pl
                        else
                            None))
            if matchedPerView |> List.exists List.isEmpty then
                []
            else
                matchedPerView
                |> List.concat
                |> List.distinctBy (fun pl -> pl.Identity)
        if namedByAnyViewUse then
            fromViewUses
        else
            boundary.SharedBufferPlacements.Values
            |> Seq.filter (fun pl ->
                importMatchesConsumerRole revision imp pl
                && (imp.Parameters
                    |> List.exists (fun (formal, scalar) ->
                        match scalar with
                        | Fidelity.PSG.BoundaryScalar.ResourceHandle(decl, false)
                            when decl = formal && imp.DeclarationFacts.ContainsKey formal ->
                            imp.SourceTypes
                            |> Map.exists (fun k srcTy ->
                                k = formal && typeMatchesPlacement revision srcTy pl)
                        | _ -> false)))
            |> Seq.toList
            |> List.distinctBy (fun pl -> pl.Identity)

    /// Resolve a non-null shared-buffer struct formal parameter on a boundary consumer import.
    let sharedBufferFormalStructTypeAt (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) (formal: Fidelity.PSG.NodeId) (nullable: bool) : Result<MLIRType, string> =
        if nullable || not (imp.DeclarationFacts.ContainsKey formal) || not (List.exists (fun (f, _) -> f = formal) imp.Parameters) then
            Error "Formal parameter is not a non-null parameter of this import."
        else
            let placements = placementsForConsumerImport revision imp
            if placements.IsEmpty then
                Error "Import is not a published shared-buffer consumer import."
            else
                match imp.SourceTypes.TryFind formal with
                | Some srcTy ->
                    if placements |> List.forall (typeMatchesPlacement revision srcTy) then
                        sharedBufferStructTypeAt revision srcTy
                    else
                        Error "Formal parameter SourceType does not match the consumer import's shared-buffer placement."
                | None -> Error "Formal parameter lacks its published SourceType."

    let isSharedBufferFormalAt (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) (formal: Fidelity.PSG.NodeId) (nullable: bool) : bool =
        match sharedBufferFormalStructTypeAt revision imp formal nullable with
        | Ok _ -> true
        | Error _ -> false

    /// Resolve the shared-buffer TStruct result carrier of a region-acquisition import.
    let sharedBufferAcquisitionStructTypeAt (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) : Result<MLIRType, string> =
        let boundary = revision.Emission.Boundary
        let isAcqResultScalar =
            match imp.Result with
            | Some(Fidelity.PSG.BoundaryScalar.Integer(bits, false)) when bits > 0 -> true
            | Some(Fidelity.PSG.BoundaryScalar.ResourceHandle(_, false)) -> true
            | _ -> false
        if not isAcqResultScalar || not (imp.DeclarationFacts.ContainsKey imp.Binding) then
            Error "Import result is not a non-null shared-buffer region handle."
        else
            let matchingViews =
                boundary.SharedBufferViewUses.Values
                |> Seq.filter (fun vu ->
                    boundary.Calls
                    |> Map.exists (fun cid acqCall ->
                        cid = vu.RegionAcquisitionCall && acqCall.Import = imp.Identity))
                |> Seq.toList
            match matchingViews with
            | _ :: _ ->
                let matchingViewTypes =
                    matchingViews
                    |> List.map (fun vu -> vu.ElementType)
                    |> List.distinct
                let matchedPlacementsPerView =
                    matchingViews
                    |> List.map (fun vu ->
                        boundary.SharedBufferPlacements
                        |> Map.toList
                        |> List.choose (fun (pid, pl) ->
                            if pid = vu.PlacementDeclaration
                               && importMatchesRegionBinding revision imp pl.RegionDescriptor.Acquire then
                                Some pl
                            else
                                None))
                let matchingPlacements =
                    if matchedPlacementsPerView |> List.exists List.isEmpty then
                        []
                    else
                        matchedPlacementsPerView
                        |> List.concat
                        |> List.distinctBy (fun pl -> pl.Identity)
                match matchingViewTypes with
                | [ elemType ] when not matchingPlacements.IsEmpty
                                    && (matchingPlacements |> List.forall (typeMatchesPlacement revision elemType)) ->
                    sharedBufferStructTypeAt revision elemType
                | _ -> Error "Region-acquisition import is claimed by disagreeing shared-buffer element types or placements."
            | [] ->
                let matchingPlacements =
                    boundary.SharedBufferPlacements.Values
                    |> Seq.filter (fun pl ->
                        importMatchesRegionBinding revision imp pl.RegionDescriptor.Acquire)
                    |> Seq.toList
                if matchingPlacements.IsEmpty then
                    Error "Import is not a published shared-buffer region acquisition."
                else
                    match imp.SourceTypes.TryFind imp.Binding with
                    | Some fnTy ->
                        let retTy = returnTypeOfSignature fnTy
                        if matchingPlacements |> List.forall (typeMatchesPlacement revision retTy) then
                            sharedBufferStructTypeAt revision retTy
                        else
                            Error "Shared-buffer acquisition import return type does not match its placement StructDescriptor."
                    | None -> Error "Shared-buffer acquisition import lacks its published binding SourceType."

    let isSharedBufferAcquisitionImport (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) : bool =
        match sharedBufferAcquisitionStructTypeAt revision imp with
        | Ok _ -> true
        | Error _ -> false

    /// Validate that every shared-buffer struct parameter or return type on `imp` has a valid published role.
    let validateSharedBufferFormalsIn (revision: Fidelity.PSG.Revision) (imp: Fidelity.PSG.BoundaryImport) : Result<unit, string> =
        let rec checkParams = function
            | [] ->
                let returnsSharedStruct =
                    imp.SourceTypes
                    |> Map.exists (fun k fnTy ->
                        k = imp.Binding && isSharedBufferStructType revision (returnTypeOfSignature fnTy))
                if returnsSharedStruct && not (isSharedBufferAcquisitionImport revision imp) then
                    Error (sprintf "Import '%s' returns a shared-buffer struct type without a valid region-acquisition role." imp.Symbol)
                else
                    Ok ()
            | (formal, scalar) :: rest ->
                let isSharedStructFormal =
                    imp.SourceTypes
                    |> Map.exists (fun k srcTy -> k = formal && isSharedBufferStructType revision srcTy)
                if isSharedStructFormal then
                    let validRole =
                        match scalar with
                        | Fidelity.PSG.BoundaryScalar.ResourceHandle(decl, false) when decl = formal ->
                            isSharedBufferFormalAt revision imp formal false
                        | _ -> false
                    if validRole then
                        checkParams rest
                    else
                        let (Fidelity.PSG.NodeId formalId) = formal
                        Error (sprintf "Import '%s' carries shared-buffer formal %d without a valid non-null shared-buffer consumer role." imp.Symbol formalId)
                else
                    checkParams rest
        checkParams imp.Parameters

    /// True when `declaration` is a shared-buffer region acquisition or consumer import.
    let isSharedBufferImport (revision: Fidelity.PSG.Revision) (declaration: Fidelity.PSG.BoundaryImport) : bool =
        isSharedBufferAcquisitionImport revision declaration
        || not ((placementsForConsumerImport revision declaration).IsEmpty)
        || (declaration.Parameters |> List.exists (fun (formal, scalar) ->
            match scalar with
            | Fidelity.PSG.BoundaryScalar.ResourceHandle(decl, false) ->
                decl = formal && isSharedBufferFormalAt revision declaration formal false
            | _ -> false))

    /// True when an import carries a non-shared-buffer opaque resource handle.
    let importCarriesNonSharedResourceHandle (revision: Fidelity.PSG.Revision) (declaration: Fidelity.PSG.BoundaryImport) : bool =
        let boundary = revision.Emission.Boundary
        let paramHasOpaqueResource (formal, scalar) =
            match scalar with
            | Fidelity.PSG.BoundaryScalar.ResourceHandle(decl, false)
                when decl = formal && isSharedBufferFormalAt revision declaration formal false ->
                false
            | _ -> hasResourceCarrierSeen boundary Set.empty scalar
        let resultHasOpaqueResource =
            if isSharedBufferAcquisitionImport revision declaration then false
            else declaration.Result |> Option.exists (hasResourceCarrierSeen boundary Set.empty)
        (declaration.Parameters |> List.exists paramHasOpaqueResource)
        || resultHasOpaqueResource

    let tryParametersInRevision (revision: Fidelity.PSG.Revision) (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        let boundary = revision.Emission.Boundary
        let rec collect ordinal acc = function
            | [] -> Ok (List.rev acc)
            | (formal, Fidelity.PSG.BoundaryScalar.Entry invocation) :: rest ->
                match boundary.CallbackInvocations.TryFind invocation with
                | Some row when row.Identity = invocation && row.Import = declaration.Identity &&
                                row.Formal = formal && row.Parameter = ordinal ->
                    match tryCallbackSignatureTypeAt revision invocation with
                    | Ok ty -> collect (ordinal + 1) (ty :: acc) rest
                    | Error reason -> Error reason
                | _ -> Error "A callback receiver parameter differs from its exact invocation, import, formal or ordinal."
            | (formal, Fidelity.PSG.BoundaryScalar.ResourceHandle(decl, false)) :: rest
                when decl = formal ->
                match sharedBufferFormalStructTypeAt revision declaration formal false with
                | Ok structTy -> collect (ordinal + 1) (structTy :: acc) rest
                | Error _ -> Error "A resource carrier requires its exact direct-call conversion and cleanup accounts."
            | (_, scalar) :: rest ->
                match tryScalarTypeIn boundary Set.empty scalar with
                | Ok ty -> collect (ordinal + 1) (ty :: acc) rest
                | Error reason -> Error reason
        collect 0 [] declaration.Parameters

    let tryResultsInRevision (revision: Fidelity.PSG.Revision) (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        let boundary = revision.Emission.Boundary
        if isSharedBufferAcquisitionImport revision declaration then
            sharedBufferAcquisitionStructTypeAt revision declaration |> Result.map List.singleton
        else
            match declaration.Result with
            | None -> Ok []
            | Some ret -> tryScalarTypeIn boundary Set.empty ret |> Result.map List.singleton

    /// Validate a boundary call's participation in a shared-buffer view use.
    /// Returns `Ok(isSharedCall, isSharedAcquisitionCall)`.
    let validateSharedBufferCallAt (revision: Fidelity.PSG.Revision) (call: Fidelity.PSG.BoundaryCall) : Result<bool * bool, string> =
        let boundary = revision.Emission.Boundary
        let (Fidelity.PSG.NodeId callSiteId) = call.Site
        let matchingViews =
            boundary.SharedBufferViewUses.Values
            |> Seq.filter (fun vu ->
                vu.RegionAcquisitionCall = call.Site
                || vu.RegionReleaseCall = Some call.Site
                || List.contains call.Site vu.SyncCalls
                || List.contains call.Site vu.ForeignUseCalls)
            |> Seq.toList
        let callsSharedImport =
            boundary.Imports
            |> Map.exists (fun impId imp ->
                impId = call.Import && isSharedBufferImport revision imp)
        if matchingViews.IsEmpty && not callsSharedImport then
            Ok(false, false)
        elif call.Resource.IsSome then
            Error (sprintf "Shared-buffer boundary call %d cannot carry resource lifetime adaptation." callSiteId)
        else
            match sharedBufferIntegrityIn revision with
            | Error reason -> Error reason
            | Ok () ->
                match matchingViews with
                | [ vu ] when vu.Copies = 0 -> Ok(true, vu.RegionAcquisitionCall = call.Site)
                | [ _ ] ->
                    Error (sprintf "Shared-buffer boundary call %d has non-zero copy count." callSiteId)
                | [] ->
                    Error (sprintf "Shared-buffer boundary call %d lacks its published BoundarySharedBufferViewUse account." callSiteId)
                | _ ->
                    Error (sprintf "Shared-buffer boundary call %d is claimed by multiple BoundarySharedBufferViewUse accounts." callSiteId)

    /// Transitively resolve PSG origin nodes across published AliasTargets and BindingUses.
    let private resolveOriginNodes (revision: Fidelity.PSG.Revision) (startId: Fidelity.PSG.NodeId) : Set<Fidelity.PSG.NodeId> =
        let aliasPairs = Map.toList revision.Emission.Callable.AliasTargets
        let bindingUsePairs = Map.toList revision.SourceReadings.BindingUses
        let rec loop (visited: Set<Fidelity.PSG.NodeId>) = function
            | [] -> visited
            | currId :: rest ->
                if Set.contains currId visited then
                    loop visited rest
                else
                    let visited' = Set.add currId visited
                    let aliasNext =
                        aliasPairs
                        |> List.choose (fun (k, v) -> if k = currId && v <> currId then Some v else None)
                    let bindingNext =
                        bindingUsePairs
                        |> List.choose (fun (k, u) -> if k = currId && u.Binding <> currId then Some u.Binding else None)
                    loop visited' (aliasNext @ bindingNext @ rest)
        loop Set.empty [ startId ]

    let private matchesSharedBufferOrigin (revision: Fidelity.PSG.Revision) (structId: Fidelity.PSG.NodeId) (vu: Fidelity.PSG.BoundarySharedBufferViewUse) : bool =
        Set.contains vu.RegionAcquisitionCall (resolveOriginNodes revision structId)

    let private hasSharedBufferCarrierType (revision: Fidelity.PSG.Revision) (nodeId: Fidelity.PSG.NodeId) : bool =
        resolveOriginNodes revision nodeId
        |> Set.exists (fun id ->
            revision.Emission.Numeric.SourceTypes
            |> Map.exists (fun k srcTy -> k = id && isSharedBufferStructType revision srcTy))

    /// True when `structId` originates from or carries a zero-copy shared-buffer region view.
    let isSharedBufferOrigin (revision: Fidelity.PSG.Revision) (structId: Fidelity.PSG.NodeId) : bool =
        (revision.Emission.Boundary.SharedBufferViewUses.Values
         |> Seq.exists (matchesSharedBufferOrigin revision structId))
        || hasSharedBufferCarrierType revision structId

    /// Validate a FieldGet or FieldSet projection on a shared-buffer struct view fail-closed.
    let validateSharedBufferProjectionAt
        (revision: Fidelity.PSG.Revision)
        (site: Fidelity.PSG.NodeId)
        (structId: Fidelity.PSG.NodeId)
        (fieldName: string)
        (isWrite: bool)
        : Result<unit, string> =
        let boundary = revision.Emission.Boundary
        let (Fidelity.PSG.NodeId siteId) = site
        let siteListed (vu: Fidelity.PSG.BoundarySharedBufferViewUse) =
            List.contains site vu.ViewProjections || List.contains site vu.WriteProjections
        let originMatched (vu: Fidelity.PSG.BoundarySharedBufferViewUse) =
            matchesSharedBufferOrigin revision structId vu
        let isSharedProjection =
            (boundary.SharedBufferViewUses.Values
             |> Seq.exists (fun vu -> siteListed vu || originMatched vu))
            || hasSharedBufferCarrierType revision structId
        if not isSharedProjection then
            Ok ()
        else
            let matching =
                boundary.SharedBufferViewUses.Values
                |> Seq.filter (fun vu -> siteListed vu || originMatched vu)
                |> Seq.toList
            match matching with
            | [ vu ] ->
                if not (originMatched vu) then
                    Error (sprintf "Shared-buffer projection at node %d disagrees with its region acquisition view use." siteId)
                elif vu.Copies <> 0 then
                    Error (sprintf "Shared-buffer projection at node %d violates zero-copy contract (Copies = %d)." siteId vu.Copies)
                elif isWrite && not (List.contains site vu.WriteProjections) then
                    Error (sprintf "Shared-buffer write projection at node %d is missing from BoundarySharedBufferViewUse.WriteProjections." siteId)
                elif not isWrite && not (List.contains site vu.ViewProjections) then
                    Error (sprintf "Shared-buffer read projection at node %d is missing from BoundarySharedBufferViewUse.ViewProjections." siteId)
                else
                    match boundary.SharedBufferPlacements.TryFind vu.PlacementDeclaration with
                    | None ->
                        let (Fidelity.PSG.NodeId plRawId) = vu.PlacementDeclaration
                        Error (sprintf "Shared-buffer projection at node %d references missing placement %d." siteId plRawId)
                    | Some pl ->
                        let isReadOnly =
                            pl.Placement.SpaceDescriptor.Access = "ReadOnly"
                            || pl.Placement.ViewLayout.Access = BAREWire.Hardware.AccessKind.ReadOnly
                            || pl.Space.Access = BAREWire.Platform.Access.ReadOnly
                        let isWriteOnly =
                            pl.Placement.SpaceDescriptor.Access = "WriteOnly"
                            || pl.Placement.ViewLayout.Access = BAREWire.Hardware.AccessKind.WriteOnly
                            || pl.Space.Access = BAREWire.Platform.Access.WriteOnly
                        match pl.Placement.StructLayout.Layout.Fields |> Array.tryFind (fun f -> f.Name = fieldName) with
                        | None ->
                            Error (sprintf "Shared-buffer projection at node %d references unknown field '%s'." siteId fieldName)
                        | Some fDesc ->
                            if isWrite && (isReadOnly || fDesc.Access = BAREWire.Hardware.AccessKind.ReadOnly) then
                                Error (sprintf "Shared-buffer write projection at node %d on field '%s' violates ReadOnly permission." siteId fieldName)
                            elif not isWrite && (isWriteOnly || fDesc.Access = BAREWire.Hardware.AccessKind.WriteOnly) then
                                Error (sprintf "Shared-buffer read projection at node %d on field '%s' violates WriteOnly permission." siteId fieldName)
                            else
                                sharedBufferIntegrityIn revision
            | _ ->
                Error (sprintf "Shared-buffer projection at node %d lacks a unique BoundarySharedBufferViewUse account." siteId)

module NativeEntrySlotSymbols =
    open Fidelity.PSG

    // Spelling only: source inventory and typed slot incidence remain authority.
    let names =
        function
        | ProgramStorageIdentity.BindingSlot binding ->
            let suffix = NodeId.value binding
            Ok (sprintf "__clef_native_entry_slot_store_%d" suffix, sprintf "__clef_native_entry_slot_load_%d" suffix)
        | ProgramStorageIdentity.Allocation _ ->
            Error "A native entry slot requires a source binding-slot identity."

module IntrinsicWriteAbi =
    let bufferType (declaration: Fidelity.PSG.IntrinsicWriteImport) =
        TMemRef(TInt(IntWidth declaration.ByteRepresentation.Bits))

    let parameters (declaration: Fidelity.PSG.IntrinsicWriteImport) : Result<MLIRType list, string> =
        match BoundaryAbi.scalarType declaration.Fd, BoundaryAbi.scalarType declaration.Count with
        | Ok fdTy, Ok countTy -> Ok [fdTy; bufferType declaration; countTy]
        | Error reason, _ | _, Error reason -> Error reason

    let results (declaration: Fidelity.PSG.IntrinsicWriteImport) : Result<MLIRType list, string> =
        BoundaryAbi.scalarType declaration.Result |> Result.map List.singleton

/// Structural serialization order only; source meaning remains in the PSG.
module OperationStructure =
    let flatten (operations: MLIROp list) : MLIROp list =
        operations
        |> List.unfold (function
            | [] -> None
            | operation :: remaining ->
                let children =
                    match operation with
                    | FuncOp(FuncDef(_, _, _, body, _))
                    | NoUnwindFunction(FuncDef(_, _, _, body, _))
                    | HWOp(HWModule(_, _, _, body))
                    | Block(_, body)
                    | Region body
                    | SMTOp(SMTSolver body) -> body
                    | SCFOp(If(_, yes, no, _)) -> yes @ Option.defaultValue [] no
                    | SCFOp(While(condition, body)) -> condition @ body
                    | SCFOp(For(_, _, _, _, body)) -> body
                    | SCFOp(IndexSwitch(_, cases, fallback, _)) -> (cases |> List.collect snd) @ fallback
                    | _ -> []
                Some(operation, children @ remaining))
