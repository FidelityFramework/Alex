/// MLIRAtomics - Atomic MLIR operation emission
///
/// INTERNAL: Witnesses CANNOT import this. Only Patterns can.
/// Provides atomic MLIR op construction via XParsec-compatible interface.
module internal Alex.Elements.MLIRAtomics

open XParsec.Combinators // parser { }
open Alex.XParsec.PSGCombinators
open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize

// Elements accept type from caller - patterns know the type and pass it explicitly

// ═══════════════════════════════════════════════════════════
// PORTABLE MLIR STRUCT OPERATIONS (MemRef-based)
// ═══════════════════════════════════════════════════════════

/// ExtractValue - memref.load with int field index
/// Emits constant + load operations
let pExtractValue (ssa: SSA) (structMemref: SSA) (fieldIndex: int) (offsetSSA: SSA) (ty: MLIRType) : PSGParser<MLIROp list> =
    parser {
        do! emitTrace "pExtractValue" (sprintf "ssa=%s, memref=%s, field=%d, ty=%s" (ssaToString ssa) (ssaToString structMemref) fieldIndex (describeType ty))
        let offsetOp = ArithOp.ConstI (offsetSSA, (NumericLiteralI.FromString (string fieldIndex)), TIndex) |> MLIROp.ArithOp
        let loadOp = MemRefOp.Load (ssa, structMemref, [offsetSSA], ty, TMemRefStatic (1, ty)) |> MLIROp.MemRefOp
        return [offsetOp; loadOp]
    }

/// InsertValue - memref.store with int field index
/// Emits constant + store operations
let pInsertValue (resultSSA: SSA) (structMemref: SSA) (value: SSA) (fieldIndex: int) (offsetSSA: SSA) (ty: MLIRType) : PSGParser<MLIROp list> =
    parser {
        do! emitTrace "pInsertValue" (sprintf "result=%s, memref=%s, value=%s, field=%d, ty=%s" (ssaToString resultSSA) (ssaToString structMemref) (ssaToString value) fieldIndex (describeType ty))
        let offsetOp = ArithOp.ConstI (offsetSSA, (NumericLiteralI.FromString (string fieldIndex)), TIndex) |> MLIROp.ArithOp
        let memrefType = TMemRefStatic (1, ty)  // 1-element struct field storage
        let storeOp = MemRefOp.Store (value, structMemref, [offsetSSA], ty, memrefType) |> MLIROp.MemRefOp
        return [offsetOp; storeOp]
    }

// ═══════════════════════════════════════════════════════════
// TYPED FIELD ACCESS VIA memref.reinterpret_cast
// Portable across all targets: CPU → GEP, FPGA → typed port, NPU → typed channel
// Zero data conversion — metadata-only cast creates typed view at byte offset
// ═══════════════════════════════════════════════════════════

/// memref.reinterpret_cast keeps the element type and the base of its source. A field of
/// another element type, or at a byte offset, is read and written through memref.view
/// (pTypedExtractView, pTypedInsertView), whose offset value the Pattern names.
let private pSameElementAtBase (name: string) (byteOffset: int) (fieldType: MLIRType) (srcType: MLIRType) : PSGParser<unit> =
    let element =
        match srcType with
        | TMemRef element | TMemRefStatic (_, element) | TMemRefScalar element -> Some element
        | _ -> None
    ensure (element = Some fieldType && byteOffset = 0)
        (sprintf "%s: memref.reinterpret_cast reads a field of the source element type at offset 0; got field %s at offset %d of %s"
            name (describeType fieldType) byteOffset (describeType srcType))

/// Byte storage guarantees only byte alignment; typed views must preserve it.
/// Typed field extraction from byte-level memref via memref.reinterpret_cast
/// Uses 3 SSAs (pulled from coeffects): viewSSA, zeroSSA, resultSSA
let pTypedExtract (resultSSA: SSA) (structMemref: SSA) (byteOffset: int) (viewSSA: SSA) (zeroSSA: SSA) (fieldType: MLIRType) (srcType: MLIRType) : PSGParser<MLIROp list> =
    parser {
        do! emitTrace "pTypedExtract" (sprintf "result=%s, memref=%s, offset=%d, fieldTy=%s" (ssaToString resultSSA) (ssaToString structMemref) byteOffset (describeType fieldType))
        do! pSameElementAtBase "pTypedExtract" byteOffset fieldType srcType
        let destType = TMemRefStatic (1, fieldType)
        let castOp = MemRefOp.ReinterpretCast (viewSSA, structMemref, byteOffset, 1, srcType, destType) |> MLIROp.MemRefOp
        let zeroOp = ArithOp.ConstI (zeroSSA, 0I, TIndex) |> MLIROp.ArithOp
        let loadOp = MemRefOp.LoadAligned (resultSSA, viewSSA, [zeroSSA], fieldType, destType, 1) |> MLIROp.MemRefOp
        return [castOp; zeroOp; loadOp]
    }

/// Typed field insertion into byte-level memref via memref.reinterpret_cast
/// Uses 2 SSAs (pulled from coeffects): viewSSA, zeroSSA — store produces no SSA
let pTypedInsert (structMemref: SSA) (value: SSA) (byteOffset: int) (viewSSA: SSA) (zeroSSA: SSA) (fieldType: MLIRType) (srcType: MLIRType) : PSGParser<MLIROp list> =
    parser {
        do! emitTrace "pTypedInsert" (sprintf "memref=%s, value=%s, offset=%d, fieldTy=%s" (ssaToString structMemref) (ssaToString value) byteOffset (describeType fieldType))
        do! pSameElementAtBase "pTypedInsert" byteOffset fieldType srcType
        let destType = TMemRefStatic (1, fieldType)
        let castOp = MemRefOp.ReinterpretCast (viewSSA, structMemref, byteOffset, 1, srcType, destType) |> MLIROp.MemRefOp
        let zeroOp = ArithOp.ConstI (zeroSSA, 0I, TIndex) |> MLIROp.ArithOp
        let storeOp = MemRefOp.StoreAligned (value, viewSSA, [zeroSSA], fieldType, destType, 1) |> MLIROp.MemRefOp
        return [castOp; zeroOp; storeOp]
    }

/// Typed field extraction via memref.view — for DIFFERENT element types (e.g., byte buffer → i64)
/// Uses 4 SSAs: offsetSSA (byte offset const), viewSSA, zeroSSA, resultSSA
let pTypedExtractView (resultSSA: SSA) (structMemref: SSA) (byteOffset: int) (offsetSSA: SSA) (viewSSA: SSA) (zeroSSA: SSA) (fieldType: MLIRType) (srcType: MLIRType) : PSGParser<MLIROp list> =
    parser {
        do! emitTrace "pTypedExtractView" (sprintf "result=%s, memref=%s, offset=%d, fieldTy=%s" (ssaToString resultSSA) (ssaToString structMemref) byteOffset (describeType fieldType))
        let destType = TMemRefStatic (1, fieldType)
        let offsetOp = ArithOp.ConstI (offsetSSA, (NumericLiteralI.FromString (string byteOffset)), TIndex) |> MLIROp.ArithOp
        let viewOp = MemRefOp.View (viewSSA, structMemref, offsetSSA, srcType, destType) |> MLIROp.MemRefOp
        let zeroOp = ArithOp.ConstI (zeroSSA, 0I, TIndex) |> MLIROp.ArithOp
        let loadOp = MemRefOp.LoadAligned (resultSSA, viewSSA, [zeroSSA], fieldType, destType, 1) |> MLIROp.MemRefOp
        return [offsetOp; viewOp; zeroOp; loadOp]
    }

/// Typed field insertion via memref.view — for DIFFERENT element types (e.g., byte buffer → i64)
/// Uses 3 SSAs: offsetSSA (byte offset const), viewSSA, zeroSSA — store produces no SSA
let pTypedInsertView (structMemref: SSA) (value: SSA) (byteOffset: int) (offsetSSA: SSA) (viewSSA: SSA) (zeroSSA: SSA) (fieldType: MLIRType) (srcType: MLIRType) : PSGParser<MLIROp list> =
    parser {
        do! emitTrace "pTypedInsertView" (sprintf "memref=%s, value=%s, offset=%d, fieldTy=%s" (ssaToString structMemref) (ssaToString value) byteOffset (describeType fieldType))
        let destType = TMemRefStatic (1, fieldType)
        let offsetOp = ArithOp.ConstI (offsetSSA, (NumericLiteralI.FromString (string byteOffset)), TIndex) |> MLIROp.ArithOp
        let viewOp = MemRefOp.View (viewSSA, structMemref, offsetSSA, srcType, destType) |> MLIROp.MemRefOp
        let zeroOp = ArithOp.ConstI (zeroSSA, 0I, TIndex) |> MLIROp.ArithOp
        let storeOp = MemRefOp.StoreAligned (value, viewSSA, [zeroSSA], fieldType, destType, 1) |> MLIROp.MemRefOp
        return [offsetOp; viewOp; zeroOp; storeOp]
    }

/// Undef - NOW USES memref.alloca (uninitialized allocation)
/// SEMANTIC CHANGE: Creates memref in stack memory instead of undef SSA value
/// Semantically equivalent: uninitialized memory = undef value
let pUndef (ssa: SSA) (ty: MLIRType) : PSGParser<MLIROp> =
    parser {
        do! emitTrace "pUndef" (sprintf "ssa=%s, ty=%s" (ssaToString ssa) (describeType ty))
        // Allocate uninitialized memref (semantically equivalent to undef)
        return MLIROp.MemRefOp (MemRefOp.Alloca (ssa, ty, None))
    }

/// ConstI - caller provides type
let pConstI (ssa: SSA) (value: bigint) (ty: MLIRType) : PSGParser<MLIROp> =
    parser {
        do! emitTrace "pConstI" (sprintf "ssa=%s, value=%s, ty=%s" (ssaToString ssa) (string value) (describeType ty))
        return MLIROp.ArithOp (ArithOp.ConstI (ssa, value, ty))
    }

/// ConstF - caller provides type
let pConstF (ssa: SSA) (value: float) (ty: MLIRType) : PSGParser<MLIROp> =
    parser {
        return MLIROp.ArithOp (ArithOp.ConstF (ssa, value, ty))
    }

/// GlobalString - module-level string constant
let pGlobalString (name: string) (content: string) (byteLength: int) (obligations: string list) : PSGParser<MLIROp> =
    parser {
        return GlobalString (name, content, byteLength, obligations)
    }

