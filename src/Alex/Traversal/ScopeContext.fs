/// ScopeContext - Principled scope management for operation accumulation
///
/// This module implements explicit scope context threading (Nanopass-style) to
/// ensure operations accumulate in their correct scope without post-processing.
///
/// ARCHITECTURAL PRINCIPLE: Operations know their scope at creation time.
/// No subtraction, no reordering, no brittle list manipulation.
///
/// Inspired by:
/// - Nanopass Framework (Scheme): Explicit state threading through scope boundaries
/// - MLIR mlir-hs: Region builder monads with isolated scopes
/// - Composer Codata principle: Witnesses observe, patterns emit, elements are atomic
module Alex.Traversal.ScopeContext

open Alex.Dialects.Core.Types

/// Scope level determines which operations are valid at this level
type ScopeLevel =
    | ModuleLevel       // Top-level: FuncDef, GlobalString, FuncDecl
    | FunctionLevel     // Inside func.func: local operations (arith, memref, etc.)
    | BlockLevel        // Inside scf.if/while/for: control flow operations

/// Per-traversal monotonic counter for operation-scope identities.
/// Owned by the root ScopeContext created on traversal entry and shared
/// exclusively across its nested child scopes (no process-global state).
[<NoEquality; NoComparison>]
type private ScopeIdSequence = {
    mutable Next: int64
}

/// Scope context tracks operations accumulated at a specific scope level
/// Forms a hierarchy: child scopes nest within parent scopes
[<NoEquality; NoComparison>]
type ScopeContext = private {
    ScopeId: int64
    ScopeLevel: ScopeLevel
    ScopeOperations: MLIROp list    // Accumulated ops at THIS level
    ScopeParent: ScopeContext option // Parent scope for nesting
    Sequence: ScopeIdSequence
} with
    member this.Id = this.ScopeId
    member this.Level = this.ScopeLevel
    member this.Operations = this.ScopeOperations
    member this.Parent = this.ScopeParent

module ScopeContext =
    /// Create root module-level scope owning a fresh per-traversal identity sequence.
    let root () : ScopeContext =
        let sequence = { Next = 1L }
        { ScopeId = 1L
          ScopeLevel = ModuleLevel
          ScopeOperations = []
          ScopeParent = None
          Sequence = sequence }

    /// Create child scope (for function bodies, control flow)
    ///
    /// Child scopes accumulate operations independently of their parent and
    /// allocate their identity on entry from the traversal's own scope sequence.
    /// When witnessing completes, operations are extracted and wrapped in a
    /// structural operation (FuncDef, SCFOp) which is added to the parent.
    ///
    /// This ensures operations never appear in multiple scopes.
    let createChild (parent: ScopeContext) (level: ScopeLevel) : ScopeContext =
        let nextId = parent.Sequence.Next + 1L
        parent.Sequence.Next <- nextId
        { ScopeId = nextId
          ScopeLevel = level
          ScopeOperations = []
          ScopeParent = Some parent
          Sequence = parent.Sequence }

    /// Add single operation to current scope
    ///
    /// Operations are accumulated in reverse order (newest first) for efficiency.
    /// Call getOps to retrieve them in correct order.
    let addOp (op: MLIROp) (scope: ScopeContext) : ScopeContext =
        { scope with ScopeOperations = op :: scope.ScopeOperations }

    /// Add multiple operations to current scope
    ///
    /// Operations are added in the order they appear in the list.
    /// Input list is reversed before prepending to maintain correct order.
    let addOps (ops: MLIROp list) (scope: ScopeContext) : ScopeContext =
        { scope with ScopeOperations = (List.rev ops) @ scope.ScopeOperations }

    /// Get all operations from this scope in correct order
    ///
    /// Operations are accumulated newest-first (cons onto list head),
    /// so we reverse to get def-before-use order.
    let getOps (scope: ScopeContext) : MLIROp list =
        List.rev scope.ScopeOperations

    /// Get parent scope (for unwinding after witnessing body)
    ///
    /// Returns None for root scope.
    let getParent (scope: ScopeContext) : ScopeContext option =
        scope.ScopeParent

    /// Check if scope is root (module-level)
    let isRoot (scope: ScopeContext) : bool =
        scope.ScopeParent.IsNone && scope.ScopeLevel = ModuleLevel

    /// Get scope depth (0 = root, 1 = function, 2 = nested block, etc.)
    let rec depth (scope: ScopeContext) : int =
        match scope.ScopeParent with
        | None -> 0
        | Some parent -> 1 + depth parent
