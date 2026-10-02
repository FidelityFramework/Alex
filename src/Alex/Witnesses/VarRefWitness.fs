/// VarRefWitness - Witness variable reference nodes
///
/// Variable references forward immutable values or load mutable binding cells.
/// The binding SSA is looked up from the accumulator (bindings witnessed first in post-order).
///
/// Function values retain separate code/environment operands. Named code in
/// value position receives a func.constant at this actual source occurrence.
///
/// NANOPASS: This witness handles ONLY VarRef nodes.
/// All other nodes return WitnessOutput.skip for other nanopasses to handle.
module Alex.Witnesses.VarRefWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.MemRefPatterns  // pLoadMutableVariable
open Alex.Patterns.CallablePatterns
open Alex.Patterns.MutableCallablePatterns
open Alex.Patterns.SequencePatterns
open Alex.Patterns.LazyPatterns
open Alex.Dialects.Core.Types  // TMemRef
open XParsec
open XParsec.Parsers
open XParsec.Combinators

// ═══════════════════════════════════════════════════════════
// CATEGORY-SELECTIVE WITNESS (Private)
// ═══════════════════════════════════════════════════════════

/// Witness variable reference nodes - forwards binding's SSA
let private witnessVarRef (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    let callable pattern =
        match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
        | Result.Error reason -> WitnessOutput.error $"Callable reference: {reason}"
    let directCallee (position: Alex.Traversal.PSGZipper.PSGZipper) =
        match Alex.Traversal.PSGZipper.up position with
        | Some parent ->
            match parent.Focus.Kind with
            | SemanticKind.Application(callee, _) -> callee = position.Focus.Id
            | _ -> false
        | None -> false
    let rec assignmentTarget (position: Alex.Traversal.PSGZipper.PSGZipper) =
        match Alex.Traversal.PSGZipper.up position with
        | Some parent ->
            match parent.Focus.Kind with
            | SemanticKind.Set(target, _) -> target = position.Focus.Id
            | SemanticKind.TypeAnnotation(inner, _) when inner = position.Focus.Id -> assignmentTarget parent
            | _ -> false
        | None -> false
    match tryMatch pVarRef ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
    | Some ((name, bindingIdOpt), _) ->
        match bindingIdOpt with
        | Some bindingId ->
            let valueShape = Alex.Traversal.CallableOperands.valueShape ctx node.Id
            let shapeError = match valueShape with Result.Error reason -> Some reason | Result.Ok _ -> None
            // Observe the reference's published value shape.
            match ctx.Graph.SourceReadings.BindingUses.TryFind node.Id with
            | Some account when account.Binding <> bindingId ->
                WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "VarRef") (Some "binding use")
                    $"PSG settlement (BindingUses) names binding {NodeId.value account.Binding} for VarRef '{name}' at node {NodeId.value node.Id}, whose source reference names {NodeId.value bindingId}."
            | Some account when account.IsProgramSlotIntent && not account.HasProgramSlotAuthority ->
                WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "VarRef") (Some "program storage")
                    $"PSG settlement (BindingUses) did not admit physical program slot authority for binding {NodeId.value bindingId} read by VarRef '{name}' at node {NodeId.value node.Id}."
            | Some account when isLazyValue ctx node ->
                match account.Class with
                | SourceBindingClass.MutableCell ->
                    WitnessOutput.error $"Lazy reference '{name}' requires an admitted pair storage read."
                | _ ->
                    let pattern =
                        if account.IsProgramSlotIntent then pProgramLazyReference ctx bindingId
                        else pLazyForward ctx bindingId
                    match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                    | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                    | Result.Error reason -> WitnessOutput.error $"Lazy reference '{name}': {reason}"
            | Some account when isSequenceValue ctx node ->
                match account.Class with
                | SourceBindingClass.MutableCell ->
                    WitnessOutput.error $"Sequence reference '{name}' requires an admitted pair storage read."
                | _ ->
                    let pattern =
                        if account.IsProgramSlotIntent then pProgramSequenceReference ctx bindingId
                        else pSequenceForward ctx bindingId
                    match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                    | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                    | Result.Error reason -> WitnessOutput.error $"Sequence reference '{name}': {reason}"
            | Some _ when shapeError.IsSome ->
                WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "VarRef") (Some "value shape")
                    $"PSG settlement (WitnessEmission callable) did not settle the value shape for VarRef '{name}' at node {NodeId.value node.Id}: {shapeError.Value}"
            | Some account when valueShape = Result.Ok(CallableValueShape.Callable node.Id) ->
                let declaration = account.IsCallableDeclaration
                match account.Class with
                | SourceBindingClass.MutableCell when assignmentTarget ctx.Zipper ->
                    // Naming the destination is not a value demand. The write
                    // witness recalls its shared cell directly.
                    { InlineOps = []; TopLevelOps = []; Result = TRVoid }
                | SourceBindingClass.MutableCell ->
                    match MLIRAccumulator.recallCallableCell bindingId ctx.Accumulator with
                    | None -> WitnessOutput.error $"VarRef '{name}': Binding not yet witnessed"
                    | Some _ -> callable (pReadMutableCallable ctx bindingId node.Id)
                | _ when account.IsPartialApplication ->
                    { InlineOps = []; TopLevelOps = []; Result = TRVoid }
                | _ when declaration && directCallee ctx.Zipper ->
                    // The direct invocation consumes the settled declaration
                    // symbol. This actual callee occurrence needs no SSA value.
                    // Transparent wrappers consume an actual typed operand,
                    // so their child occurrences retain normal value transport.
                    { InlineOps = []; TopLevelOps = []; Result = TRVoid }
                | _ when account.IsProgramSlotIntent ->
                    callable (pProgramCallableReference ctx bindingId)
                | _ ->
                    match MLIRAccumulator.recallCallable bindingId ctx.Accumulator with
                    | Some _ -> callable (pCallableForward ctx bindingId)
                    | None when declaration -> callable (pNamedCallable ctx)
                    | None -> callable (pCallableForward ctx bindingId)
            | Some account ->
                // Baker states the resolved reference's binding use. The binding
                // body may belong to another resident or imported scope.
                match account.Class with
                | SourceBindingClass.Formal ->
                    // Check accumulator first — match arm Var bindings are bound to
                    // the scrutinee SSA by MatchWitness, not pre-assigned in coeffects.
                    match MLIRAccumulator.recallNode bindingId ctx.Accumulator with
                    | Some (ssa, ty) ->
                        // An occurrence-bound formal still has its parameter
                        // carrier. Transcribe this read's settled refinement,
                        // just as on the coeffect lookup path below.
                        let (ops, readSSA, readTy) = adaptOperand ctx.Coeffects ctx.Graph node.Id node.Id ssa ty
                        { InlineOps = ops; TopLevelOps = []; Result = TRValue { SSA = readSSA; Type = readTy } }
                    | None ->
                        // A formal's value and carrier are source-published.
                        let patternBindingPattern =
                            parser {
                                let! ssa = getNodeSSA bindingId
                                let ty = mapTypeAt bindingId ctx
                                let! (meetOps, readSSA, readTy) = pAdapt node.Id node.Id ssa ty
                                return (meetOps, TRValue { SSA = readSSA; Type = readTy })
                            }

                        match tryMatchWithDiagnostics patternBindingPattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                        | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                        | Result.Error reason ->
                            WitnessOutput.errorCoded AX3002 (Some node.Id) (Some "VarRef") (Some "PatternBinding")
                                $"PSG settlement (SSA assignment) did not settle a value for PatternBinding {NodeId.value bindingId} read by VarRef '{name}' at node {NodeId.value node.Id}: {reason}"

                | SourceBindingClass.ImmutableValue | SourceBindingClass.MutableCell ->
                    // Immutable Lambda bindings forward their function value. A mutable
                    // binding's initializer does not change the cell-load contract.
                    let isMut = account.Class = SourceBindingClass.MutableCell
                    let isFunctionBinding = account.IsFunctionBinding

                    if not isMut && isFunctionBinding then
                        if directCallee ctx.Zipper then
                            { InlineOps = []; TopLevelOps = []; Result = TRVoid }
                        else WitnessOutput.error $"Callable reference '{name}' has no concrete settled value carrier."
                    elif account.IsProgramSlotIntent then
                        // Module-level value: reload from its slot (valid in any function)
                        // the slot's element type at the binding's range width on fabric
                        let represented = try Result.Ok(mapTypeAt bindingId ctx) with ex -> Result.Error ex.Message
                        match represented with
                        | Result.Error reason ->
                            WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "VarRef") (Some "program storage")
                                $"PSG settlement (BindingUses) lacks the physical representation of program slot {NodeId.value bindingId} read by VarRef '{name}': {reason}"
                        | Result.Ok valueTy ->
                            let globalName = ModuleValues.globalName account.Name bindingId
                            match tryMatchWithDiagnostics (pGlobalSlotLoad bindingId node.Id globalName valueTy)
                                          ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                            | Result.Ok ((ops, TRValue v), _) ->
                                let (meetOps, readSSA, readTy) = adaptOperand ctx.Coeffects ctx.Graph node.Id node.Id v.SSA v.Type
                                { InlineOps = ops @ meetOps; TopLevelOps = []; Result = TRValue { SSA = readSSA; Type = readTy } }
                            | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                            | Result.Error diagnostic -> WitnessOutput.error $"VarRef '{name}': {diagnostic}"
                    elif account.IsPartialApplication then
                        // Partial application binding - no value SSA available
                        // ApplicationWitness handles saturated calls through the coeffect
                        { InlineOps = []; TopLevelOps = []; Result = TRVoid }
                    else
                        // Value binding - post-order: binding already witnessed, recall its SSA
                        match MLIRAccumulator.recallNode bindingId ctx.Accumulator with
                        | Some (ssa, ty) ->
                            // Auto-load ONLY if the Binding is mutable (isMut from PSG).
                            // Mutable bindings hold memref<1xT> cells that need memref.load.
                            // Immutable bindings (including MemRef.alloca results) forward as-is.
                            if isMut then
                                // Mutable cell — extract element type for auto-load
                                let elemTypeOpt =
                                    match ty with
                                    | TMemRef elemType -> Some elemType
                                    | TMemRefStatic (_, elemType) -> Some elemType
                                    | _ -> None
                                match elemTypeOpt with
                                | Some elemType ->
                                    let (NodeId nodeIdInt) = node.Id
                                    match tryMatchWithDiagnostics (pLoadMutableVariable nodeIdInt ssa elemType)
                                                  ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                                    | Result.Ok ((ops, TRValue v), _) ->
                                        // the cell's width, then this read's own (ruling 3: a read
                                        // refined under a guard truncates; at a boundary it extends)
                                        let (meetOps, readSSA, readTy) = adaptOperand ctx.Coeffects ctx.Graph node.Id node.Id v.SSA v.Type
                                        { InlineOps = ops @ meetOps; TopLevelOps = []; Result = TRValue { SSA = readSSA; Type = readTy } }
                                    | Result.Ok ((ops, result), _) ->
                                        { InlineOps = ops; TopLevelOps = []; Result = result }
                                    | Result.Error diagnostic ->
                                        WitnessOutput.error $"VarRef '{name}': {diagnostic}"
                                | None ->
                                    WitnessOutput.error $"VarRef '{name}': Mutable cell has unexpected type {ty}"
                            else
                                // Immutable value (including buffers): forward, at this read's own width
                                let (meetOps, readSSA, readTy) = adaptOperand ctx.Coeffects ctx.Graph node.Id node.Id ssa ty
                                { InlineOps = meetOps; TopLevelOps = []; Result = TRValue { SSA = readSSA; Type = readTy } }
                        | None ->
                            WitnessOutput.error $"VarRef '{name}': Binding not yet witnessed"

            | None ->
                WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "VarRef") (Some "binding use")
                    $"PSG settlement (BindingUses) omitted the source-owned binding use for VarRef '{name}' at node {NodeId.value node.Id}."
        | None ->
            WitnessOutput.error $"VarRef '{name}': No binding ID (unresolved reference)"
    | None ->
        WitnessOutput.skip

// ═══════════════════════════════════════════════════════════
// NANOPASS REGISTRATION (Public)
// ═══════════════════════════════════════════════════════════

/// VarRef nanopass - witnesses variable references
let nanopass : Nanopass = {
    Name = "VarRef"
    Witness = witnessVarRef
}
