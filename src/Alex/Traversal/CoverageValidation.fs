/// CoverageValidation - Detect unwitnessed reachable PSG nodes
///
/// After the shared traversal, validate all source-authorized executable and
/// declaration-scope occurrences. Source-published proof-only nodes do not execute.
///
/// This validation ensures no PSG nodes "fall through" silently without MLIR generation.
module Alex.Traversal.CoverageValidation

open Fidelity.PSG
open Alex.Traversal.TransferTypes

// ═══════════════════════════════════════════════════════════
// COVERAGE VALIDATION
// ═══════════════════════════════════════════════════════════

/// Source publication owns both executable demand and declaration placement.
let private sourceOccurrences (graph: Revision) =
    let projection = graph.Emission
    let proofOnly = Set.unionMany [projection.Ordinary.DeferredOnly; projection.Boundary.DeclarationOnly; projection.Spatial.MetadataOnly]
    let intrinsicScopes = projection.Boundary.IntrinsicWriteImports.Values |> Seq.map _.Scope |> Set.ofSeq
    graph.Nodes.Values
    |> Seq.filter (fun node ->
        (node.IsReachable || projection.Boundary.ByScope.ContainsKey node.Id || intrinsicScopes.Contains node.Id ||
         projection.Spatial.Required.Contains node.Id || projection.Spatial.ByScope.ContainsKey node.Id || projection.Spatial.CodeRoots.Contains node.Id)
        && not (proofOnly.Contains node.Id))
    |> Seq.map _.Id
    |> Set.ofSeq

/// Report any required source occurrence missing from the shared traversal.
let private validateCoverageWith
    (expected: Set<NodeId>)
    (graph: Revision)
    (allVisited: Set<NodeId>)  // Merged visited set from all nanopasses
    : Diagnostic list =

    let unwitnessedNodes =
        Set.difference expected allVisited
        |> Set.toList
        |> List.map (fun id -> graph.Nodes[id])

    // Generate error diagnostics for each unwitnessed node
    unwitnessedNodes
    |> List.map (fun node ->
        // Extract first line of Kind for readable error message
        let kindSummary =
            match node.Kind.ToString().Split('\n') with
            | lines when lines.Length > 0 -> lines.[0]
            | _ -> node.Kind.ToString()

        Diagnostic.error
            (Some node.Id)
            (Some "CoverageValidation")
            (Some "Unwitnessed source occurrence")
            (sprintf "Alex traversal did not witness required PSG occurrence '%s' (ID %d): no declaration root or structural parent placed it, or no witness claims its kind." kindSummary (NodeId.value node.Id)))

let validateCoverage (graph: Revision) (allVisited: Set<NodeId>) : Diagnostic list =
    validateCoverageWith (sourceOccurrences graph) graph allVisited
