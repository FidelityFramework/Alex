/// NanopassArchitecture - Nanopass framework
///
/// Each witness = one nanopass, run over a single post-order PSG traversal
/// Results overlay/fold into cohesive MLIR graph
module Alex.Traversal.NanopassArchitecture

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.ScopeContext
open Alex.Traversal.PSGZipper
open Alex.Traversal.CoverageValidation

// ═══════════════════════════════════════════════════════════════════════════
// NANOPASS TYPE
// ═══════════════════════════════════════════════════════════════════════════

/// A nanopass is a complete PSG traversal that selectively witnesses nodes
/// Single-phase post-order traversal: all witnesses run during one traversal
type Nanopass = {
    /// Nanopass name (e.g., "Literal", "Arithmetic", "ControlFlow")
    Name: string

    /// The witnessing function for this nanopass
    /// Returns skip for nodes it doesn't handle
    Witness: WitnessContext -> SemanticNode -> WitnessOutput
}

// ═══════════════════════════════════════════════════════════════════════════
// SCOPE CLASSIFICATION AND POST-ORDER TRAVERSAL
// ═══════════════════════════════════════════════════════════════════════════

/// Check if this node defines a scope boundary (owns its children)
/// Scope boundaries control recursion: scope-owning witnesses handle their own children
/// via explicit scope markers (ScopeEnter/ScopeExit) instead of automatic child traversal.
let private isScopeBoundary (node: SemanticNode) : bool =
    match node.Kind with
    | SemanticKind.Lambda _ -> true
    | SemanticKind.IfThenElse _ -> true
    | SemanticKind.ContinuationDispatch _ -> true
    | SemanticKind.WhileLoop _ -> true
    | SemanticKind.ForLoop _ -> true
    | SemanticKind.ForEach _ -> true
    | SemanticKind.Match _ -> true
    | SemanticKind.CaseElimination _ -> true
    | SemanticKind.TryWith _ -> true
    | SemanticKind.Binding (_, _, _, Some DeclRoot.HardwareModule) -> true
    | SemanticKind.Binding (_, _, _, Some DeclRoot.KernelModule) -> true
    | _ -> false

/// The regions of a scope-owning occurrence, in order, or the first error among them.
let collectRegions (regions: Result<'region, Diagnostic> list) : Result<'region list, Diagnostic> =
    List.foldBack (fun region collected ->
        match region, collected with
        | Result.Error failure, _ -> Result.Error failure
        | Result.Ok _, Result.Error failure -> Result.Error failure
        | Result.Ok value, Result.Ok values -> Result.Ok (value :: values)) regions (Result.Ok [])

/// A materialized code Lambda can be a structural child of its source
/// ClosureValue as well as its canonical named declaration. Local body walks
/// must still observe each value occurrence, but this exact code identity emits
/// one module definition. Legacy closure Lambdas also construct a value and do
/// not qualify for this reuse.
let private definitionOnlyLambda (node: SemanticNode) (graph: Revision) : bool =
    let callable = graph.Emission.Callable
    let storage = graph.Emission.Storage
    callable.DefinitionOnlyLambdas.Contains node.Id || storage.DefinitionOnlyThunks.Contains node.Id

/// The source owner identifies scalar result occurrences independently of
/// numeric declaration/slot carriers. This check cannot classify an exception
/// from a node's syntax or invent a missing representation.
let private validateNumericResult (graph: Revision) nodeId result =
    let publication = graph.Emission.Numeric
    if publication.ResultSites.Contains nodeId then
        match result with
        | TRError _ | TRSkip -> Result.Ok ()
        | TRValue value ->
            match publication.Values.TryFind nodeId with
            | None -> Result.Error (sprintf "Source Numeric publication omitted the required result carrier for node %d" (NodeId.value nodeId))
            | Some carrier ->
                try
                    let expected = Alex.CodeGeneration.TypeMapping.scalarCarrierType carrier
                    if value.Type = expected then Result.Ok ()
                    else Result.Error (sprintf "Witness result at node %d has carrier %A; source Numeric publication requires %A" (NodeId.value nodeId) value.Type expected)
                with error -> Result.Error error.Message
        | _ -> Result.Error (sprintf "Witness result at node %d omitted its source-published scalar value" (NodeId.value nodeId))
    else Result.Ok ()

/// Visit all nodes in post-order (children before parents)
/// PUBLIC: Used by Lambda/ControlFlow witnesses for sub-graph traversal
/// Post-order ensures children's SSA bindings are available when parent witnesses
let rec visitAllNodes
    (witness: WitnessContext -> SemanticNode -> WitnessOutput)
    (visitedCtx: WitnessContext)
    (currentNode: SemanticNode)
    (visited: ref<Set<NodeId>>)  // Traversal visited set (global on CPU, per-function on FPGA)
    : unit =

    // A fresh function-body scope deliberately drops local value coverage.
    // Named code declarations retain their global identity even when reached
    // through a structural occurrence rather than a VarRef dependency.
    // This lookup reads an eagerly settled CCS projection for this exact graph;
    // it performs no source incidence analysis or hyperedge query.
    let demand = visitedCtx.Graph.Emission.Ordinary
    let boundary = visitedCtx.Graph.Emission.Boundary
    let spatial = visitedCtx.Graph.Emission.Spatial
    let definitionReuse =
        if Set.contains currentNode.Id !(visitedCtx.GlobalVisited) then definitionOnlyLambda currentNode visitedCtx.Graph
        else false
    if currentNode.Id <> visitedCtx.Zipper.Focus.Id
       || not (obj.ReferenceEquals(visitedCtx.Graph, visitedCtx.Zipper.Graph)) then
        Diagnostic.error (Some currentNode.Id) (Some "Traversal") (Some "zipper occurrence")
            "The traversal node and zipper must identify the same occurrence in the current graph"
        |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
    elif demand.DeferredOnly.Contains currentNode.Id then
        ()
    elif boundary.DeclarationOnly.Contains currentNode.Id then
        ()
    elif spatial.MetadataOnly.Contains currentNode.Id then
        ()
    elif Set.contains currentNode.Id !visited then
        ()
    elif definitionReuse then
        ()
    else
        let priorErrors = visitedCtx.Accumulator.Errors
        MLIRAccumulator.forgetVoid currentNode.Id visitedCtx.Accumulator
        // Mark as visited in traversal scope
        visited := Set.add currentNode.Id !visited
        // Also track in global visited for coverage validation
        // (On CPU these are the same ref; on FPGA the local set is separate)
        visitedCtx.GlobalVisited := Set.add currentNode.Id !(visitedCtx.GlobalVisited)

        // The caller's Zipper is already focused on currentNode with correct breadcrumbs.
        // No re-rooting needed — Huet navigation maintains the path.

        // POST-ORDER Phase 1: Visit children FIRST (tree edges)
        // Read the source disposition before obtaining a body. An omitted
        // position remains an original ordinal, never a missing-body lookup.
        let declarationLeaf = boundary.DeclarationLeaves.Contains currentNode.Id ||
                              spatial.Required.Contains currentNode.Id
        if not (isScopeBoundary currentNode) && not declarationLeaf then
            let refuse reason =
                Diagnostic.error (Some currentNode.Id) (Some "Traversal") (Some "source child disposition") reason
                |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
            match visitedCtx.Graph.SourceReadings.Children.TryFind currentNode.Id with
            | None -> refuse "The current occurrence has no source-authored child disposition account."
            | Some children when children.Length <> currentNode.Children.Length ->
                refuse "The source child disposition account does not cover every original position."
            | Some children ->
                List.zip currentNode.Children children |> List.iteri (fun ordinal (childId, disposition) ->
                    let declared =
                        match disposition.Traversal with
                        | ChildTraversal.EnterLocal id | ChildTraversal.SourceOmitted(_, id)
                        | ChildTraversal.EnterImported(_, _, id) -> id
                    if disposition.Ordinal <> ordinal || declared <> childId then
                        refuse "The source child disposition differs from its original position."
                    else
                        match disposition.Traversal with
                        | ChildTraversal.SourceOmitted _ -> ()
                        | ChildTraversal.EnterImported _ ->
                            refuse "An imported child requires its installed source-authorized scope; local traversal cannot reconstruct it."
                        | ChildTraversal.EnterLocal _ ->
                            match PSGZipper.down ordinal visitedCtx.Zipper with
                            | Some childZipper ->
                                visitAllNodes witness { visitedCtx with Zipper = childZipper } childZipper.Focus visited
                            | None -> refuse (sprintf "Cannot enter source-declared local child %d at ordinal %d." (NodeId.value childId) ordinal))

        // A reference never places or emits its binding. The binding is witnessed at its own
        // settled structural position; a reference that reaches an unwitnessed binding is a
        // settlement gap reported by the reference witness, never repaired here.

        // THEN witness current node (after its structural children)
        let witnessed =
            if obj.ReferenceEquals(priorErrors, visitedCtx.Accumulator.Errors) then
                witness visitedCtx currentNode
            else
                WitnessOutput.errorCoded AX4001 (Some currentNode.Id) (Some "Traversal") (Some "required child occurrence")
                    "The parent occurrence cannot be witnessed after a required child account or witness was refused."
        // The combined registry has already tried skipped witnesses. Validate
        // the chosen result before committing its operations or recalled value.
        let numericAdmission = validateNumericResult visitedCtx.Graph currentNode.Id witnessed.Result
        let output =
            match numericAdmission with
            | Result.Ok () -> witnessed
            | Result.Error reason ->
                WitnessOutput.errorCoded AX4001 (Some currentNode.Id) (Some "Traversal") (Some "published numeric result") reason

        // InlineOps belong to the current scope, exactly where the settled graph places the node.
        let updatedCurrentScope = ScopeContext.addOps output.InlineOps !visitedCtx.ScopeContext
        visitedCtx.ScopeContext := updatedCurrentScope

        // TopLevelOps go to ROOT scope (module level: GlobalString, nested FuncDef)
        if not (List.isEmpty output.TopLevelOps) then
            EmissionCorrespondence.record visitedCtx output.TopLevelOps
            let updatedRootScope = ScopeContext.addOps output.TopLevelOps !visitedCtx.RootScopeContext
            visitedCtx.RootScopeContext := updatedRootScope

        // Drain any module-level memref.global decls queued by a StaticLifetime allocation
        // during this node's witnessing. A parser (e.g. pAllocValue for a program-lifetime
        // DU/record) cannot place a module-scope decl itself, so it queues on the accumulator;
        // draining centrally here routes them to RootScopeContext for every construction path
        // (DU, Option, List, Map, Set, Result) without each witness having to remember.
        // The queue holds what this occurrence queued. An occurrence that is refused,
        // by its witness or by the check of its result, places no declaration, and its
        // queue is emptied so that no later occurrence places it.
        let queued = MLIRAccumulator.drainPendingStaticGlobals visitedCtx.Accumulator
        let pendingStaticGlobals =
            match output.Result with
            | TRError _ -> []
            | _ -> queued
        if not (List.isEmpty pendingStaticGlobals) then
            EmissionCorrespondence.record visitedCtx pendingStaticGlobals
            let updatedRootScope = ScopeContext.addOps pendingStaticGlobals !visitedCtx.RootScopeContext
            visitedCtx.RootScopeContext := updatedRootScope

        // Bind result if value (global binding)
        match output.Result with
        | TRValue v ->
            MLIRAccumulator.bindNode currentNode.Id v.SSA v.Type visitedCtx.Accumulator
        | TRCallable value ->
            match MLIRAccumulator.bindCallable currentNode.Id value visitedCtx.Accumulator with
            | Result.Ok () -> ()
            | Result.Error reason ->
                Diagnostic.error (Some currentNode.Id) (Some "Callable") (Some "operand transport") reason
                |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
        | TRCallableCell value ->
            match MLIRAccumulator.bindCallableCell currentNode.Id value visitedCtx.Accumulator with
            | Result.Ok () -> ()
            | Result.Error reason ->
                Diagnostic.error (Some currentNode.Id) (Some "Callable") (Some "mutable storage") reason
                |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
        | TRSequence value ->
            match MLIRAccumulator.bindSequence currentNode.Id value visitedCtx.Accumulator with
            | Result.Ok () -> ()
            | Result.Error reason ->
                Diagnostic.error (Some currentNode.Id) (Some "Sequence") (Some "operand transport") reason
                |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
        | TRLazy value ->
            match MLIRAccumulator.bindLazy currentNode.Id value visitedCtx.Accumulator with
            | Result.Ok () -> ()
            | Result.Error reason ->
                Diagnostic.error (Some currentNode.Id) (Some "Lazy") (Some "operand transport") reason
                |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
        | TRVoid when obj.ReferenceEquals(priorErrors, visitedCtx.Accumulator.Errors) ->
            MLIRAccumulator.completeVoid visitedCtx.Zipper visitedCtx.ScopeContext visitedCtx.Accumulator
        | TRVoid -> ()
        | TRError diag ->
            MLIRAccumulator.addError diag visitedCtx.Accumulator
        | TRSkip ->
            // A combined witness never returns TRSkip; a traversal witness that does
            // left this node unclaimed, which is a coverage gap, not a no-op.
            Diagnostic.error (Some currentNode.Id) (Some "Traversal") (Some "witness coverage")
                (sprintf "Alex witness coverage did not claim node %d: the traversal witness returned skip" (NodeId.value currentNode.Id))
            |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator

// ═══════════════════════════════════════════════════════════════════════════
// NANOPASS REGISTRY
// ═══════════════════════════════════════════════════════════════════════════

/// Registry of all nanopasses (populated by witnesses)
type NanopassRegistry = {
    /// All registered nanopasses
    Nanopasses: Nanopass list
}

module NanopassRegistry =
    let empty = { Nanopasses = [] }

    let register (nanopass: Nanopass) (registry: NanopassRegistry) =
        { registry with Nanopasses = nanopass :: registry.Nanopasses }

    let registerAll (nanopasses: Nanopass list) (registry: NanopassRegistry) =
        { registry with Nanopasses = nanopasses @ registry.Nanopasses }

// ═══════════════════════════════════════════════════════════════════════════
// COMBINED WITNESS EXECUTION
// ═══════════════════════════════════════════════════════════════════════════

/// Combine multiple nanopass witnesses into a single witness that tries each in order
/// WITH COVERAGE VALIDATION: Reports error if no witness handles a node (prevents silent gaps)
let combineWitnesses (nanopasses: Nanopass list) : (WitnessContext -> SemanticNode -> WitnessOutput) =
    fun ctx node ->
        let rec tryWitnesses remaining =
            match remaining with
            | [] ->
                // NO WITNESS HANDLED THIS NODE - Report error for coverage validation
                // This prevents silent gaps where nodes are skipped without any witness
                // processing them, which leads to empty MLIR output.
                // Structural nodes (ModuleDef, Sequential) should have transparent witnesses.
                //
                // Enrich the error with contextual information to aid diagnosis:
                let kindStr = sprintf "%A" node.Kind
                let typeStr = sprintf "%A" node.Type
                let contextInfo =
                    match node.Kind with
                    | SemanticKind.VarRef (name, Some bindingId) ->
                        // The binding's contract need not have an executable
                        // body in this scope. Diagnostics read the same exact
                        // binding-use account as the reference witness.
                        match ctx.Graph.SourceReadings.BindingUses.TryFind node.Id with
                        | Some contract when contract.Binding = bindingId ->
                            sprintf "VarRef '%s' -> Binding %d (source declaration: %s). Type: %s"
                                name (NodeId.value bindingId) contract.Name typeStr
                        | None ->
                            sprintf "VarRef '%s' -> Binding %d (source binding-use account missing). Type: %s" name (NodeId.value bindingId) typeStr
                        | Some _ ->
                            sprintf "VarRef '%s' -> Binding %d (source binding-use account disagrees). Type: %s" name (NodeId.value bindingId) typeStr
                    | _ ->
                        sprintf "Kind: %s. Type: %s" (kindStr.Split('\n').[0]) typeStr
                WitnessOutput.error (sprintf "No witness handled node %A — %s" node.Id contextInfo)
            | nanopass :: rest ->
                let result = nanopass.Witness ctx node
                match result.Result with
                | TRSkip ->
                    // This witness doesn't handle this node kind - try next witness
                    tryWitnesses rest
                | _ ->
                    // Witness handled the node (TRValue, TRVoid, or TRError) - stop trying
                    result
        tryWitnesses nanopasses

/// Run all nanopasses in single post-order traversal with shared accumulator
let runAllNanopasses
    (nanopasses: Nanopass list)
    (graph: Revision)
    (coeffects: TransferCoeffects)
    (sharedAcc: MLIRAccumulator)
    (rootScope: ref<ScopeContext>)
    (globalVisited: ref<Set<NodeId>>)
    : unit =

    // Create combined witness that tries all nanopasses at each node
    let combinedWitness = combineWitnesses nanopasses

    let refuse nodeId part reason =
        Diagnostic.error (Some nodeId) (Some "Traversal") (Some part) reason
        |> fun diagnostic -> MLIRAccumulator.addError diagnostic sharedAcc

    // Entry placement is a Baker fact. Module membership and an open statement
    // never become a consumer census or a request for inactive bodies.
    graph.SourceReadings.Entries
    |> List.fold (fun importedScopes (entry: SourceWitnessEntry) ->
        // Even an already witnessed body or installed import must have a
        // current, complete account for every declared entry occurrence.
        let admitted =
            match RevisionNavigation.checkContext graph entry.Focus entry.Context with
            | Result.Error reason ->
                refuse entry.Focus "source entry" reason
                false
            | Result.Ok _ -> true
        if not admitted then importedScopes else
        match Revision.tryNode entry.Focus graph with
        | Some _ when globalVisited.Value.Contains entry.Focus -> importedScopes
        | Some _ ->
            match PSGZipper.createAt graph entry.Focus entry.Context with
            | None -> refuse entry.Focus "source entry" "The declared entry does not match its complete source occurrence account."
            | Some zipper ->
                let context =
                    { Graph = graph; Coeffects = coeffects; Accumulator = sharedAcc; RootAccumulator = sharedAcc
                      ScopeContext = rootScope; RootScopeContext = rootScope; Zipper = zipper
                      GlobalVisited = globalVisited; TraversalVisited = globalVisited }
                visitAllNodes combinedWitness context zipper.Focus globalVisited
            importedScopes
        | None when entry.Reason = SourceEntryReason.BoundaryScope ->
            if Set.contains entry.Focus importedScopes then importedScopes else
            match graph.SourceReadings.ContextHeaders.TryFind entry.Focus with
            | Some _ ->
                match Alex.Patterns.PlatformPatterns.boundaryImportsAt entry.Focus graph.Emission.Boundary with
                | Result.Error reason -> refuse entry.Focus "boundary owner" reason
                | Result.Ok operations -> rootScope.Value <- ScopeContext.addOps operations rootScope.Value
                Set.add entry.Focus importedScopes
            | _ ->
                refuse entry.Focus "boundary owner" "The source entry has no matching body-free context account."
                importedScopes
        | None ->
            refuse entry.Focus "source entry" "The source-authorized entry body is absent from this revision."
            importedScopes) Set.empty
    |> ignore

/// Main entry point: Execute all nanopasses and return accumulator
let executeNanopasses
    (registry: NanopassRegistry)
    (graph: Revision)
    (coeffects: TransferCoeffects)
    : MLIRAccumulator =

    if List.isEmpty registry.Nanopasses then
        // An empty registry would witness nothing and skip coverage validation.
        let accumulator = MLIRAccumulator.empty()
        Diagnostic.error None (Some "Traversal") (Some "witness registry")
            "Alex witness registry is empty for this target: no witness can claim any node"
        |> fun diagnostic -> MLIRAccumulator.addError diagnostic accumulator
        accumulator
    else
        // Create SINGLE shared accumulator for ALL nanopasses
        let sharedAcc = MLIRAccumulator.empty()

        // Create SINGLE global visited set for ALL nanopasses
        let globalVisited = ref Set.empty

        // Create root scope for operation accumulation
        let rootScope = ref (ScopeContext.root())

        // Run all nanopasses together in single traversal
        runAllNanopasses registry.Nanopasses graph coeffects sharedAcc rootScope globalVisited

        // Coverage validation - ensure all reachable nodes were witnessed
        let coverageDiagnostics = CoverageValidation.validateCoverage graph !globalVisited
        if not (List.isEmpty coverageDiagnostics) then
            // Add coverage errors to accumulator
            for diag in coverageDiagnostics do
                MLIRAccumulator.addError diag sharedAcc

        // Extract operations from root scope and add to accumulator (Phase 7)
        let rootOps = ScopeContext.getOps !rootScope
        MLIRAccumulator.addOps rootOps sharedAcc

        sharedAcc
