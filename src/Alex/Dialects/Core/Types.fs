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
let declaredWordWidth (arch: Architecture) : IntWidth =
    match arch.Register with
    | Ok bits -> IntWidth bits
    | Error message -> failwith message

/// The declared Pointer width in bytes: the size of an index, and the unit of a memref
/// descriptor (five words). Function code values have no implicit data-storage layout.
let declaredPointerBytes (arch: Architecture) : int =
    match arch.Pointer with
    | Ok bits -> (bits + 7) / 8
    | Error message -> failwith message

/// The size in bytes of a value as it is stored: a read, never a computation (§8.3, one size
/// model). A scalar is the bytes of its selected width; every pointer-sized type (an index; a
/// rank-1 memref descriptor, {allocPtr, alignPtr, offset, size, stride}, five words)
/// is the declared Pointer width times its words, and `pointer` is `Error`
/// where no declaration is in hand (serialization), so that a pointer-sized value reaching such a
/// path is a loud defect and never a silent eight bytes; a struct is its settled size, read from
/// the layout CCS settled at saturation, and a struct with none (fabric, an opaque field) is a
/// stop. A width the range was to give (`IntWidth 0`) has no size and is a stop naming it.
let rec mlirTypeSizeWith (pointer: Result<int, string>) (ty: MLIRType) : int =
    let pointerBytes () =
        match pointer with
        | Ok bits -> (bits + 7) / 8
        | Error message -> failwith message
    match ty with
    | TInt (IntWidth 0) -> failwith "mlirTypeSize: an integer whose width the node's range was to give reached a size read unnarrowed"
    | TInt w -> intWidthBytes w
    | TFloat F32 -> 4 | TFloat F64 -> 8
    | TOpaqueHandle _ | TResourceOption _ -> failwith "mlirTypeSize: an opaque resource cannot acquire generic spatial storage authority"
    | TFunc _ -> failwith "mlirTypeSize: a function code SSA has no admitted data-storage layout; settle callable storage before sizing it"
    | TMemRef _ | TMemRefStatic _ | TMemRefScalar _ -> 5 * pointerBytes ()
    | TVector (count, _) ->
        failwithf "mlirTypeSize: PSG settlement (Layouts) did not settle a storage size for a vector of %d lanes; no size is read for it" count
    | TIndex -> pointerBytes ()
    | TStruct (_, Some bytes) -> bytes.Size
    | TStruct (fields, None) ->
        failwithf "mlirTypeSize: the struct {%s} has no settled layout to read its size from (a fabric struct, or a field the placement could not settle)"
            (fields |> List.map fst |> String.concat ", ")
    | TSeqClock -> failwith "mlirTypeSize: a clock signal (!seq.clock) has no byte storage; a fabric value reached a size read"
    | TTag caseCount ->
        failwithf "mlirTypeSize: backend (CIRCT) did not settle a byte size for the abstract tag of %d cases: a fabric tag's width is the hw backend's, and a core holds a tag as a byte memref" caseCount
    | TVoid -> failwith "mlirTypeSize: TVoid marks a foreign function with no result; it is not a value and has no size"

/// The settled byte offset of a struct's field, read from the layout CCS settled; a struct with
/// no settled layout, or a field outside it, is a stop.
let structFieldOffset (ty: MLIRType) (fieldIndex: int) : int =
    match ty with
    | TStruct (_, Some bytes) ->
        match List.tryItem fieldIndex bytes.Offsets with
        | Some offset -> offset
        | None -> failwithf "structFieldOffset: field %d is outside the settled layout of %d fields" fieldIndex bytes.Offsets.Length
    | TStruct (fields, None) ->
        failwithf "structFieldOffset: the struct {%s} has no settled layout to read an offset from" (fields |> List.map fst |> String.concat ", ")
    | other -> failwithf "structFieldOffset: %A is not a struct" other

/// The size model read through the architecture's declared Pointer width.
let mlirTypeSize (arch: Architecture) (ty: MLIRType) : int =
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
        | Fidelity.PSG.BoundaryScalar.Integer(bits, _) -> TInt(IntWidth bits)
        | Fidelity.PSG.BoundaryScalar.Boolean -> TInt(IntWidth 1)
        | Fidelity.PSG.BoundaryScalar.Entry _ -> invalidArg "scalar" "An entry carrier requires its source-published receiving signature."
        | Fidelity.PSG.BoundaryScalar.ResourceHandle _ ->
            invalidArg "scalar" "A resource carrier requires its exact direct-call conversion and cleanup accounts."
        | Fidelity.PSG.BoundaryScalar.WritableBytes _ ->
            invalidArg "scalar" "A writable byte carrier requires its exact source-published declaration."
        | Fidelity.PSG.BoundaryScalar.ReadOnlyBytes _ ->
            invalidArg "scalar" "A read-only byte carrier requires its exact source-published declaration."
        | Fidelity.PSG.BoundaryScalar.BorrowedBytes _ ->
            invalidArg "scalar" "A borrowed result view carrier requires its exact source-published declaration."

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

    let rec signatureTypeIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) (signature: Fidelity.PSG.NativeEntrySignature) =
        if signature.CallingConvention <> "CDecl" then
            invalidArg "signature" "A closed native entry requires its source-published CDecl convention."
        TFunc(List.map (scalarTypeIn boundary) signature.Parameters, signature.Result |> Option.map (scalarTypeIn boundary) |> Option.toList)

    and signatureType (signature: Fidelity.PSG.NativeEntrySignature) =
        if signature.CallingConvention <> "CDecl" then
            invalidArg "signature" "A closed native entry requires its source-published CDecl convention."
        TFunc(List.map scalarType signature.Parameters, signature.Result |> Option.map scalarType |> Option.toList)

    and scalarTypeIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) scalar =
        match tryScalarTypeIn boundary Set.empty scalar with
        | Ok ty -> ty
        | Error reason -> invalidArg "scalar" reason

    let tryParametersIn (boundary: Fidelity.PSG.BoundaryEmissionProjection) (declaration: Fidelity.PSG.BoundaryImport) : Result<MLIRType list, string> =
        let rec collect acc = function
            | [] -> Ok (List.rev acc)
            | (_, scalar) :: rest ->
                match tryScalarTypeIn boundary Set.empty scalar with
                | Ok ty -> collect (ty :: acc) rest
                | Error reason -> Error reason
        collect [] declaration.Parameters

    let parametersIn boundary (declaration: Fidelity.PSG.BoundaryImport) =
        declaration.Parameters |> List.map (snd >> scalarTypeIn boundary)

    let resultsIn boundary (declaration: Fidelity.PSG.BoundaryImport) =
        declaration.Result |> Option.map (scalarTypeIn boundary) |> Option.toList

    let parameters (declaration: Fidelity.PSG.BoundaryImport) =
        declaration.Parameters |> List.map (snd >> scalarType)

    let results (declaration: Fidelity.PSG.BoundaryImport) =
        declaration.Result |> Option.map scalarType |> Option.toList

module NativeEntrySlotSymbols =
    open Fidelity.PSG

    /// Spelling only: source inventory and typed slot incidence remain authority.
    let names =
        function
        | ProgramStorageIdentity.BindingSlot binding ->
            let suffix = NodeId.value binding
            sprintf "__clef_native_entry_slot_store_%d" suffix, sprintf "__clef_native_entry_slot_load_%d" suffix
        | ProgramStorageIdentity.Allocation _ -> invalidArg "identity" "A native entry slot requires a source binding-slot identity."

module IntrinsicWriteAbi =
    let bufferType (declaration: Fidelity.PSG.IntrinsicWriteImport) =
        TMemRef(TInt(IntWidth declaration.ByteRepresentation.Bits))

    let parameters (declaration: Fidelity.PSG.IntrinsicWriteImport) =
        [BoundaryAbi.scalarType declaration.Fd; bufferType declaration; BoundaryAbi.scalarType declaration.Count]

    let results (declaration: Fidelity.PSG.IntrinsicWriteImport) =
        [BoundaryAbi.scalarType declaration.Result]

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
