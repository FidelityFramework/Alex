/// MatchWitness - Witness CaseElimination (structural match) via XParsec
///
/// Scope witness following the Y-combinator pattern (like ControlFlowWitness).
/// Platform-agnostic — the Pattern handles TargetPlatform.
///
/// CaseElimination preserves the fold structure from Baker:
/// - Each arm's body contains Baker's selected bindings and source guards
/// - This boundary selects only the already settled shallow pattern decision
///
/// The witness walks each arm's sub-tree via witnessBranchScope,
/// then delegates to pBuildMatchElimination for assembly.
module Alex.Witnesses.MatchWitness

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.Traversal.ScopeContext
open Alex.Traversal.PSGZipper
open Alex.XParsec.PSGCombinators

open Alex.Patterns.ControlFlowPatterns

// ═══════════════════════════════════════════════════════════════════════════
// BRANCH REGION COLLECTION THROUGH THE SCOPE TRAVERSAL DRIVER
// ═══════════════════════════════════════════════════════════════════════════

/// Visit a declared child of the match from its actual occurrence. A child the
/// zipper cannot reach is an error, and the witness emits nothing for the match.
let private visitChild (childId: NodeId) (ctx: WitnessContext) combinator : Result<unit, Diagnostic> =
    let position =
        ctx.Zipper.Focus.Children |> List.tryFindIndex ((=) childId)
        |> Option.bind (fun index -> down index ctx.Zipper)
    match position with
    | Some childZipper ->
        visitAllNodes combinator { ctx with Zipper = childZipper } childZipper.Focus ctx.TraversalVisited
        Result.Ok ()
    | None ->
        Result.Error (Diagnostic.error (Some ctx.Zipper.Focus.Id) (Some "CaseElimination") (Some "structural child")
                        $"Cannot descend to declared match child {NodeId.value childId}")

/// Witness one arm body in a child scope and return its operations.
let private witnessBranchScope (rootId: NodeId) (ctx: WitnessContext) (combinator: WitnessContext -> SemanticNode -> WitnessOutput) : Result<MLIROp list, Diagnostic> =
    let branchScope = ref (ScopeContext.createChild !ctx.ScopeContext BlockLevel)
    visitChild rootId { ctx with ScopeContext = branchScope } combinator
    |> Result.map (fun () -> ScopeContext.getOps !branchScope)

/// A terminal refutable arm is selected only after Baker's requirement in this
/// exact frontier occurrence. A declaration's Parent field cannot establish it.
let private terminalAdmitted (ctx: WitnessContext) (node: SemanticNode) arms : Result<bool, string> =
    match arms with
    | [{ Pattern = Pattern.Const _ | Pattern.Union _ }] ->
        let projection = ctx.Graph.Emission.Storage
        let requirement =
            projection.PatternRequirements.TryFind node.Id |> Option.bind projection.Requirements.TryFind
        match requirement, ctx.Zipper.Path with
        | Some contract, step :: _ ->
            Result.Ok (
                step.Parent = contract.Frontier && step.Port = OccurrencePort.StructuralChild
                && step.Ordinal = 1 && step.Extent = 2
                && (ctx.Graph.SourceReadings.Ports.TryFind (step.Parent, step.Port)
                    |> Option.exists (fun account ->
                        account.Stamp = step.Stamp && account.Extent = step.Extent
                        && account.Positions.TryFind 0 = Some contract.Site
                        && account.Positions.TryFind 1 = Some node.Id))
                && Set.contains contract.Site ctx.TraversalVisited.Value
                && (MLIRAccumulator.recallNode contract.Site ctx.Accumulator |> Option.exists (fun (_, ty) ->
                    ty = mapTypeAt contract.Site ctx)))
        | _ -> Result.Ok false
    | _ -> Result.Ok true

// ═══════════════════════════════════════════════════════════════════════════
// MATCH WITNESS
// ═══════════════════════════════════════════════════════════════════════════

let private witnessMatchWith (getCombinator: unit -> (WitnessContext -> SemanticNode -> WitnessOutput)) (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    let combinator = getCombinator()

    match tryMatch pCaseElimination ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
    | Some ((_, arms), _) when arms |> List.exists (fun arm -> not arm.Bindings.IsEmpty || arm.Guard.IsSome) ->
        WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "CaseElimination") (Some "selected scope")
            "Baker must settle pattern bindings and guards inside the selected body before witnessing"
    | Some ((scrutineeId, arms), _) ->
        match terminalAdmitted ctx node arms with
        | Result.Error reason ->
            WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "CaseElimination") (Some "terminal requirement") reason
        | Result.Ok false ->
            WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "CaseElimination") (Some "terminal requirement")
                "The terminal pattern decision is outside its validated requirement frontier"
        | Result.Ok true ->

        // Step 1: Visit scrutinee in CURRENT scope (like ControlFlowWitness condition)
        match visitChild scrutineeId ctx combinator with
        | Result.Error failure -> WitnessOutput.errorDiag failure
        | Result.Ok () ->

        // Recall scrutinee result
        match MLIRAccumulator.recallNode scrutineeId ctx.Accumulator with
        | None ->
            WitnessOutput.error "CaseElimination: Scrutinee witnessed but no result"
        | Some (scrutineeSSA, scrutineeMLIRType) ->

            // Step 2: Pull the selected bodies through their actual occurrences.
            // Baker owns extraction and guard order inside those bodies.
            let armRegions =
                arms
                |> List.map (fun arm ->
                    witnessBranchScope arm.Body ctx combinator
                    |> Result.map (fun armOps -> armOps, arm.Body, arm))
                |> collectRegions
            match armRegions with
            | Result.Error failure -> WitnessOutput.errorDiag failure
            | Result.Ok armResults ->

            // Step 3: Determine if expression-valued. A result type CCS left as an
            // unresolved type variable is not a unit result; it is reported.
            let isUnit = Alex.Traversal.Values.isUnitTyped ctx.Graph node.Id

            let result =
                if isUnit then Result.Ok None
                else
                    let resultType = mapTypeAt node.Id ctx
                    match tryMatchWithDiagnostics (getNodeSSAs node.Id) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                    | Result.Ok (ssa :: _, _) -> Result.Ok (Some (ssa, resultType))
                    | Result.Ok ([], _) ->
                        Result.Error $"PSG settlement (SSA assignment) did not settle a result value for expression-valued CaseElimination node {NodeId.value node.Id}"
                    | Result.Error reason ->
                        Result.Error $"PSG settlement (SSA assignment) did not settle a result value for expression-valued CaseElimination node {NodeId.value node.Id}: {reason}"

            match result with
            | Result.Error reason ->
                WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "CaseElimination") (Some "result value") reason
            | Result.Ok result ->

            // Step 4: Delegate to pattern for elision — diagnostic error flow preserved
            let elimination = pBuildMatchElimination scrutineeSSA scrutineeMLIRType scrutineeId armResults result node.Id
            let pattern =
                if isUnit then Alex.Patterns.LiteralPatterns.pWithUnitResult node.Id elimination
                else elimination
            match tryMatchWithDiagnostics pattern ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
            | Result.Ok ((ops, transferResult), _) ->
                { InlineOps = ops; TopLevelOps = []; Result = transferResult }
            | Result.Error diagnostic ->
                WitnessOutput.error $"CaseElimination: {diagnostic}"

    | None -> WitnessOutput.skip

/// Create nanopass with Y-combinator for recursive sub-graph witnessing
let createNanopass (getCombinator: unit -> (WitnessContext -> SemanticNode -> WitnessOutput)) : Nanopass = {
    Name = "Match"
    Witness = witnessMatchWith getCombinator
}
