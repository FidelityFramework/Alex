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

/// Source declaration entries have their own physical completion obligation;
/// context headers never acquire executable body membership from witnessing.
let private sourceBoundaryScopes (graph: Revision) =
    graph.SourceReadings.Entries
    |> Seq.filter (fun entry -> entry.Reason = SourceEntryReason.BoundaryScope && not (graph.Nodes.ContainsKey entry.Focus))
    |> Seq.map _.Focus
    |> Set.ofSeq

/// Report any required source occurrence missing from the shared traversal.
let private validateCoverageWith
    (expected: Set<NodeId>)
    (graph: Revision)
    (allVisited: Set<NodeId>)  // Merged visited set from all nanopasses
    : Diagnostic list =

    Set.difference expected allVisited
    |> Set.toList
    |> List.map (fun identity ->
        let message =
            match graph.Nodes.TryFind identity with
            | Some node ->
                let kindSummary = node.Kind.ToString().Split('\n').[0]
                sprintf "Alex traversal did not witness required PSG occurrence '%s' (ID %d): no declaration root or structural parent placed it, or no witness claims its kind." kindSummary (NodeId.value identity)
            | None ->
                match graph.SourceReadings.ContextHeaders.TryFind identity with
                | Some header when header.Identity = identity ->
                    sprintf "Alex traversal did not witness required source boundary scope '%s' (ID %d): its assigned import plan was not successfully witnessed." header.Name (NodeId.value identity)
                | _ ->
                    sprintf "Alex traversal did not witness required source boundary scope (ID %d): its matching body-free context account is absent." (NodeId.value identity)
        Diagnostic.error
            (Some identity)
            (Some "CoverageValidation")
            (Some "Unwitnessed source occurrence")
            message)

let validateCoverage (graph: Revision) (allVisited: Set<NodeId>) : Diagnostic list =
    validateCoverageWith (sourceOccurrences graph) graph allVisited

/// Only a successful exact entry/import-plan reading creates this receipt.
/// Whole traversal and the fresh common region must discharge every assigned
/// body-free import scope independently of executable-region confinement.
let validateBoundaryCoverage (graph: Revision) (boundaryScopes: Set<NodeId>) : Diagnostic list =
    validateCoverageWith (sourceBoundaryScopes graph) graph boundaryScopes

/// The producer owns region membership; this check only restricts the same
/// whole-revision coverage obligation to those published members.
let validateRegionCoverage (graph: Revision) (members: Set<NodeId>) (visited: Set<NodeId>) : Diagnostic list =
    validateCoverageWith (Set.intersect (sourceOccurrences graph) members) graph visited
