/// ControlFlowWitness - Witness control flow operations via XParsec
///
/// Uses XParsec combinators from PSGCombinators to match PSG structure,
/// then delegates to Patterns for MLIR elision.
///
/// NANOPASS: This witness handles ONLY control flow nodes.
/// All other nodes return WitnessOutput.skip for other nanopasses to handle.
///
/// SPECIAL CASE: Control flow needs to witness sub-graphs (then/else/body branches)
/// that can contain ANY category of nodes. Uses subGraphCombinator to fold over
/// all registered witnesses.
module Alex.Witnesses.ControlFlowWitness

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Traversal.PSGZipper
open Alex.XParsec.PSGCombinators

open Alex.Patterns.ControlFlowPatterns
open Alex.Patterns.SequencePatterns
open Alex.Patterns.LazyPatterns
open Alex.Patterns.CallablePatterns

// ═══════════════════════════════════════════════════════════════════════════
// Y-COMBINATOR PATTERN
// ═══════════════════════════════════════════════════════════════════════════
//
// Scope witnesses need to handle nested scopes (e.g., IfThenElse inside WhileLoop).
// This requires recursive self-reference: the combinator must include itself.
//
// Solution: Y-combinator fixed point via thunk (unit -> Combinator)
// The combinator getter is passed from WitnessRegistry, allowing deferred evaluation
// and creating a proper fixed point where witnesses can recursively invoke themselves.

/// Witness one branch region (if-then, if-else, while-cond, while-body, for-body) in a
/// child scope and return its operations. Bindings and errors use the shared accumulator.
/// A region that is absent from the graph, or is not a declared child of the occurrence,
/// is an error. The witness that receives it emits nothing for the occurrence.
let private witnessBranchScope (rootId: NodeId) (ctx: WitnessContext) (combinator: WitnessContext -> SemanticNode -> WitnessOutput) : Result<MLIROp list, Diagnostic> =
    let failure message =
        Result.Error (Diagnostic.coded AX4001 (Some rootId) (Some "ControlFlow") (Some "structural occurrence") message)
    match Revision.tryNode rootId ctx.Graph with
    | None -> failure $"Control-flow region {NodeId.value rootId} is absent from the current graph."
    | Some branchNode ->
        let position =
            ctx.Zipper.Focus.Children
            |> List.tryFindIndex ((=) rootId)
            |> Option.bind (fun index -> down index ctx.Zipper)
        match position with
        | Some branchZipper when branchZipper.Focus.Id = rootId ->
            // Operations witnessed in the region accumulate into its own child scope.
            // The visited set is the traversal's: a node is witnessed once.
            let branchScope = ref (ScopeContext.createChild !ctx.ScopeContext BlockLevel)
            visitAllNodes combinator { ctx with Zipper = branchZipper; ScopeContext = branchScope } branchNode ctx.TraversalVisited
            Result.Ok (ScopeContext.getOps !branchScope)
        | _ -> failure $"Control-flow region {NodeId.value rootId} is not a declared child of its actual occurrence."

// ═══════════════════════════════════════════════════════════════════════════
// CATEGORY-SELECTIVE WITNESS (Private)
// ═══════════════════════════════════════════════════════════════════════════

/// Pull only the dispatch's declared child regions through the existing
/// fixed-point scope mechanism. Labels and branch identities come from Baker.
let private witnessContinuationDispatch getCombinator (ctx: WitnessContext) (node: SemanticNode) selector cases otherwise =
    let diagnostic phase message =
        WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "ContinuationDispatch") (Some phase) message
    let children = selector :: otherwise :: (cases |> List.map snd)
    match children |> List.tryFind (fun id -> Revision.tryNode id ctx.Graph |> Option.isNone) with
    | Some missing -> diagnostic "graph prerequisites" $"ContinuationDispatch {NodeId.value node.Id} references missing child {NodeId.value missing}"
    | None when children |> List.exists (fun id -> not (List.contains id node.Children)) ->
        diagnostic "graph prerequisites" $"ContinuationDispatch {NodeId.value node.Id} has an operand outside its declared structural children"
    | None ->
        let combinator = getCombinator ()
        let selectorRegion = witnessBranchScope selector ctx combinator
        let caseRegions =
            cases
            |> List.map (fun (label, body) ->
                witnessBranchScope body ctx combinator |> Result.map (fun operations -> label, body, operations))
            |> collectRegions
        let fallbackRegion = witnessBranchScope otherwise ctx combinator
        match selectorRegion, caseRegions, fallbackRegion with
        | Result.Error failure, _, _
        | _, Result.Error failure, _
        | _, _, Result.Error failure -> WitnessOutput.errorDiag failure
        | Result.Ok selectorOps, Result.Ok branches, Result.Ok fallbackOps ->
            let fallback = otherwise, fallbackOps
            let pattern =
                if isLazyValue ctx node then pLazyDispatch ctx selector branches fallback
                elif isSequenceValue ctx node then pSequenceDispatch ctx selector branches fallback
                else
                    let isUnit = Alex.Traversal.Values.isUnitTyped ctx.Graph node.Id
                    let result =
                        if isUnit then None
                        else Some (Alex.Traversal.Values.value node.Id 0, mapTypeAt node.Id ctx)
                    let dispatch = pBuildContinuationDispatch node.Id selector branches fallback result
                    if isUnit then Alex.Patterns.LiteralPatterns.pWithUnitResult node.Id dispatch else dispatch
            match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
            | Result.Ok ((operations, transfer), _) ->
                { InlineOps = selectorOps @ operations; TopLevelOps = []; Result = transfer }
            | Result.Error message -> diagnostic "settled operands" message

/// Witness control flow operations - category-selective (handles only control flow nodes)
/// Takes combinator getter (Y-combinator thunk) for recursive self-reference
let private witnessControlFlowWith (getCombinator: unit -> (WitnessContext -> SemanticNode -> WitnessOutput)) (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    // Get the full combinator (including ourselves) via Y-combinator fixed point
    let combinator = getCombinator()

    match tryMatch pIfThenElse ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
    | Some ((condId, thenId, elseIdOpt), _) ->
        // The condition is visited in the CURRENT scope: its operations precede scf.if.
        // Only the branch bodies are child scopes. IfThenElse is a scope boundary, so the
        // traversal does not visit its children; the condition is visited here.
        let conditionPosition =
            ctx.Zipper.Focus.Children |> List.tryFindIndex ((=) condId)
            |> Option.bind (fun index -> down index ctx.Zipper)
        let visitedCondition =
            match Revision.tryNode condId ctx.Graph, conditionPosition with
            | Some condNode, Some position when position.Focus.Id = condId ->
                // Keep the operation scope, but descend from the actual If
                // occurrence. Reusing its zipper would misidentify every
                // nested operand and lose its child breadcrumbs.
                visitAllNodes combinator { ctx with Zipper = position } condNode ctx.TraversalVisited
                true
            | _ -> false

        // Recall the condition at its declared occurrence. A block or an annotation is
        // bound to the value it forwards by its own witness.
        match if visitedCondition then MLIRAccumulator.recallNode condId ctx.Accumulator else None with
        | None when not visitedCondition ->
            WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "ControlFlow") (Some "IfThenElse condition")
                $"PSG settlement did not place condition {NodeId.value condId} of IfThenElse {NodeId.value node.Id} in the graph as a declared child of its occurrence"
        | None ->
            WitnessOutput.error "IfThenElse: Condition witnessed but no result"
        | Some (condSSA, condType) ->
            // The branches are child scopes. The Pattern composes them for the selected
            // platform (scf.if regions, or inline operations and comb.mux).
            let thenRegion = witnessBranchScope thenId ctx combinator
            let elseRegion =
                match elseIdOpt with
                | Some elseId -> witnessBranchScope elseId ctx combinator |> Result.map Some
                | None -> Result.Ok None
            match thenRegion, elseRegion with
            | Result.Error failure, _
            | _, Result.Error failure -> WitnessOutput.errorDiag failure
            | Result.Ok thenOps, Result.Ok elseOps ->

            let pattern =
                if isLazyValue ctx node then
                    match elseIdOpt, elseOps with
                    | Some elseId, Some operations ->
                        pLazyConditional ctx { SSA = condSSA; Type = condType } thenId thenOps elseId operations
                    | _ -> XParsec.Parsers.fail (XParsec.Message "Lazy conditional requires both settled branches.")
                elif isSequenceValue ctx node then
                    match elseIdOpt, elseOps with
                    | Some elseId, Some operations ->
                        pSequenceConditional ctx { SSA = condSSA; Type = condType } thenId thenOps elseId operations
                    | _ -> XParsec.Parsers.fail (XParsec.Message "Sequence conditional requires both settled branches.")
                elif isCallableValue ctx node then
                    match elseIdOpt, elseOps with
                    | Some elseId, Some operations ->
                        pCallableConditional ctx { SSA = condSSA; Type = condType } thenId thenOps elseId operations
                    | _ -> XParsec.Parsers.fail (XParsec.Message "Callable conditional requires both settled branches.")
                else
                    let isUnit = Alex.Traversal.Values.isUnitTyped ctx.Graph node.Id
                    let build result = pBuildConditional condSSA thenOps elseOps thenId elseIdOpt result node.Id
                    if isUnit then Alex.Patterns.LiteralPatterns.pWithUnitResult node.Id (build None)
                    else
                        let resultType = mapTypeAt node.Id ctx
                        // A valued conditional carries its derived result value; an absent one is
                        // a settlement defect, never a unit conditional.
                        XParsec.Combinators.parser {
                            let! ssas = getNodeSSAs node.Id
                            match ssas with
                            | ssa :: _ -> return! build (Some (ssa, resultType))
                            | [] ->
                                return! XParsec.Parsers.fail (XParsec.Message
                                    $"PSG settlement did not derive a result value for valued IfThenElse {NodeId.value node.Id}")
                        }
            match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
            | Result.Ok ((ops, transferResult), _) ->
                { InlineOps = ops; TopLevelOps = []; Result = transferResult }
            | Result.Error diagnostic ->
                WitnessOutput.error $"IfThenElse: {diagnostic}"

    | None ->
        match tryMatch pWhileLoop ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Some ((condId, bodyId), _) ->
            let condRegion = witnessBranchScope condId ctx combinator
            let bodyRegion = witnessBranchScope bodyId ctx combinator
            match condRegion, bodyRegion with
            | Result.Error failure, _
            | _, Result.Error failure -> WitnessOutput.errorDiag failure
            | Result.Ok condOps, Result.Ok bodyOps ->

            // Recall condition result to build scf.condition terminator
            match MLIRAccumulator.recallNode condId ctx.Accumulator with
            | None ->
                WitnessOutput.error "WhileLoop: Condition witnessed but no result"
            | Some (condSSA, _) ->
                let loop = pBuildWhileLoop condSSA condOps bodyOps
                let pattern =
                    if Alex.Traversal.Values.isUnitTyped ctx.Graph node.Id then
                        Alex.Patterns.LiteralPatterns.pWithUnitResult node.Id loop
                    else loop
                match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                | Result.Ok ((ops, result), _) ->
                    { InlineOps = ops; TopLevelOps = []; Result = result }
                | Result.Error diagnostic -> WitnessOutput.error $"WhileLoop: {diagnostic}"

        | None ->
            match tryMatch pForLoop ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
            | Some ((_, lowerId, upperId, _, bodyId), _) ->
                match MLIRAccumulator.recallNode lowerId ctx.Accumulator, MLIRAccumulator.recallNode upperId ctx.Accumulator with
                | Some _, Some _ ->
                    match witnessBranchScope bodyId ctx combinator with
                    | Result.Error failure -> WitnessOutput.errorDiag failure
                    | Result.Ok _ -> WitnessOutput.error "ForLoop needs step constant - gap in patterns"

                | _ -> WitnessOutput.error "ForLoop: Loop bounds not yet witnessed"

            | None -> WitnessOutput.skip

// ═══════════════════════════════════════════════════════════════════════════
// NANOPASS REGISTRATION (Public)
// ═══════════════════════════════════════════════════════════════════════════

/// Create control flow nanopass with Y-combinator thunk for recursive self-reference
/// The combinator getter allows deferred evaluation, creating a fixed point where
/// this witness can handle nested control flow (e.g., IfThenElse inside WhileLoop)
let createNanopass (getCombinator: unit -> (WitnessContext -> SemanticNode -> WitnessOutput)) : Nanopass = {
    Name = "ControlFlow"
    Witness = fun ctx node ->
        match node.Kind with
        | SemanticKind.ContinuationDispatch (selector, cases, otherwise) ->
            witnessContinuationDispatch getCombinator ctx node selector cases otherwise
        | _ -> witnessControlFlowWith getCombinator ctx node
}
