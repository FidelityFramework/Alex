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
        // Navigate down to each child via PSGZipper.down — preserves breadcrumbs.
        let declarationLeaf = boundary.DeclarationLeaves.Contains currentNode.Id ||
                              spatial.Required.Contains currentNode.Id
        if not (isScopeBoundary currentNode) && not declarationLeaf then
            let omittedActuals =
                demand.Calls.TryFind currentNode.Id
                |> Option.map (fun call -> Set.difference call.Omitted call.Eager)
                |> Option.defaultValue Set.empty
            currentNode.Children |> List.iteri (fun childIndex childId ->
                if childIndex > 0 && omittedActuals.Contains(childIndex - 1) then () else
                match Revision.tryNode childId visitedCtx.Graph with
                | Some childNode when not childNode.IsReachable ->
                    // Reachability is CCS's decision, read here: a child the graph marks unreachable
                    // (a module's quotation declaration, D9; anything nothing executes) is not witnessed.
                    ()
                | Some childNode ->
                    // Navigate zipper DOWN to this child — builds path with parent breadcrumb
                    match PSGZipper.down childIndex visitedCtx.Zipper with
                    | Some childZipper ->
                        let childCtx = { visitedCtx with Zipper = childZipper }
                        visitAllNodes witness childCtx childNode visited
                    | None ->
                        Diagnostic.error (Some currentNode.Id) (Some "Traversal") (Some "structural child")
                            $"Cannot descend to declared child {NodeId.value childId} at index {childIndex}"
                        |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
                | None ->
                    Diagnostic.error (Some currentNode.Id) (Some "Traversal") (Some "structural child")
                        $"Declared child {NodeId.value childId} is absent from the current graph"
                    |> fun diagnostic -> MLIRAccumulator.addError diagnostic visitedCtx.Accumulator
            )

        // A reference never places or emits its binding. The binding is witnessed at its own
        // settled structural position; a reference that reaches an unwitnessed binding is a
        // settlement gap reported by the reference witness, never repaired here.

        // THEN witness current node (after its structural children)
        let witnessed = witness visitedCtx currentNode
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
let private combineWitnesses (nanopasses: Nanopass list) : (WitnessContext -> SemanticNode -> WitnessOutput) =
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
                        // For VarRef: show what the binding resolves to
                        match Revision.tryNode bindingId ctx.Graph with
                        | Some bindingNode ->
                            let bindingChildKind =
                                bindingNode.Children
                                |> List.tryHead
                                |> Option.bind (fun cid -> Revision.tryNode cid ctx.Graph)
                                |> Option.map (fun cn -> sprintf "%A" cn.Kind |> fun s -> s.Split('\n').[0])
                                |> Option.defaultValue "no children"
                            sprintf "VarRef '%s' -> Binding %d (child: %s). Type: %s" name (NodeId.value bindingId) bindingChildKind typeStr
                        | None ->
                            sprintf "VarRef '%s' -> Binding %d (not found in graph). Type: %s" name (NodeId.value bindingId) typeStr
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

    // Publication authorizes import declaration scopes separately from runtime
    // reachability. A declaration-only module still owns its physical imports.
    let boundaryScopes =
        let boundary = graph.Emission.Boundary
        Set.union (boundary.ByScope.Keys |> Set.ofSeq)
                  (boundary.IntrinsicWriteImports.Values |> Seq.map _.Scope |> Set.ofSeq)
    let spatial = graph.Emission.Spatial
    let sourceRoots = Set.unionMany [boundaryScopes; spatial.ByScope.Keys |> Set.ofSeq; spatial.Required; spatial.CodeRoots]

    // Process a single structural root node
    let processRoot (nodeId: NodeId) =
        if not (Set.contains nodeId !globalVisited) then
            match Revision.tryNode nodeId graph with
            | Some node when node.IsReachable || sourceRoots.Contains nodeId ->
                match PSGZipper.create graph nodeId with
                | None ->
                    Diagnostic.error (Some nodeId) (Some "Traversal") (Some "root occurrence")
                        (sprintf "Alex traversal could not focus declared root %d in the current graph" (NodeId.value nodeId))
                    |> fun diagnostic -> MLIRAccumulator.addError diagnostic sharedAcc
                | Some initialZipper ->
                    let nodeCtx = {
                        Graph = graph
                        Coeffects = coeffects
                        Accumulator = sharedAcc
                        RootAccumulator = sharedAcc
                        ScopeContext = rootScope
                        RootScopeContext = rootScope
                        Zipper = initialZipper
                        GlobalVisited = globalVisited
                        TraversalVisited = globalVisited  // Default: same as global; LambdaWitness overrides on FPGA
                    }
                    visitAllNodes combinedWitness nodeCtx node globalVisited
            | Some _ ->
                // Reachability is CCS's decision: an unreachable root is not witnessed.
                ()
            | None ->
                Diagnostic.error (Some nodeId) (Some "Traversal") (Some "root occurrence")
                    (sprintf "PSG settlement (DeclarationRoots/ModuleClassifications) names root %d, which is absent from the current graph" (NodeId.value nodeId))
                |> fun diagnostic -> MLIRAccumulator.addError diagnostic sharedAcc

    // The graph's declaration roots own execution. In particular, Baker's
    // startup root contains its ordered initializer spine; a witness never
    // discovers or schedules initialization from lexical module membership.
    for codeRoot in spatial.CodeRoots do
        processRoot codeRoot
    for nodeId, _ in graph.DeclarationRoots do
        processRoot nodeId
    for KeyValue(moduleId, classification) in graph.ModuleClassifications do
        for definition in classification.Definitions do
            processRoot definition
        processRoot moduleId
    for scope in sourceRoots do
        processRoot scope

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
