/// PSGZipper - True Huet Zipper for PSG Navigation
///
/// A zipper is a data structure for navigating and modifying immutable trees.
/// It pairs your current focus with a path (breadcrumbs) showing how you got there.
///
/// References:
/// - Huet, "The Zipper" (1997) - original paper
/// - Tomas Petricek, "Tree zipper query expressions" - F# computation expressions
/// - Mark Seemann, "Zippers" (2024) - bidirectional navigation in functional code
///
/// CANONICAL ARCHITECTURE (January 2026):
/// The PSGZipper is PURELY navigational. It contains:
/// - Focus: The current SemanticNode we're examining
/// - Path: Breadcrumbs recording siblings left behind when navigating down
/// - Graph: The full SemanticGraph for node lookups
///
/// NOTHING ELSE goes in the zipper. Coeffects and accumulator state are separate.
/// See: docs/Single_Flattening_Design.md
module Alex.Traversal.PSGZipper

open Fidelity.PSG

// ═══════════════════════════════════════════════════════════════════════════
// ZIPPER PATH (Breadcrumbs)
// ═══════════════════════════════════════════════════════════════════════════

/// A single step in the path, recording what we left behind when going down.
/// When navigating to child N, we record:
/// - The parent node we came from
/// - The siblings to the left of our chosen child
/// - The siblings to the right of our chosen child
type PathStep = OccurrenceBreadcrumb

/// The path from root to current focus (list of steps, most recent first)
type ZipperPath = PathStep list

// ═══════════════════════════════════════════════════════════════════════════
// PSG ZIPPER (Pure Navigation)
// ═══════════════════════════════════════════════════════════════════════════

/// The PSG Zipper - true Huet zipper for NAVIGATION ONLY
/// 
/// ARCHITECTURAL INVARIANT: This type contains Focus, Path, and Graph.
/// NO coeffects. NO accumulator state. NO mutable fields.
type PSGZipper = {
    /// The current focus node
    Focus: SemanticNode

    /// Path back to root (breadcrumbs)
    Path: ZipperPath

    /// The full semantic graph (for node lookups)
    Graph: Revision
}

// ═══════════════════════════════════════════════════════════════════════════
// ZIPPER CREATION
// ═══════════════════════════════════════════════════════════════════════════

/// Focus an exact source-authored occurrence. Context identities need not have
/// executable bodies; the source port account preserves their correspondence.
let createAt (graph: Revision) (focusId: NodeId) (path: ZipperPath) : PSGZipper option =
    match Revision.tryNode focusId graph, RevisionNavigation.checkContext graph focusId path with
    | Some node, Result.Ok _ -> Some { Focus = node; Path = path; Graph = graph }
    | _ -> None

/// A body with several actual occurrences requires an explicit path. Neither
/// a missing inventory nor an ambiguous one permits re-rooting the zipper.
let create (graph: Revision) (focusId: NodeId) : PSGZipper option =
    match graph.SourceReadings.Contexts.TryFind focusId with
    | Some [path] -> createAt graph focusId path
    | _ -> None

/// Create a zipper at the first declaration root
let fromEntryPoint (graph: Revision) : PSGZipper option =
    graph.SourceReadings.Entries
    |> List.tryPick (fun entry -> createAt graph entry.Focus entry.Context)

// ═══════════════════════════════════════════════════════════════════════════
// NAVIGATION
// ═══════════════════════════════════════════════════════════════════════════

/// Move UP to the parent node
/// Returns None if already at root
let up (z: PSGZipper) : PSGZipper option =
    match z.Path with
    | [] -> None  // At root, cannot go up
    | step :: restPath ->
        createAt z.Graph step.Parent restPath

/// Move DOWN to a specific child by index
/// Records siblings left behind in the path
let down (childIndex: int) (z: PSGZipper) : PSGZipper option =
    match RevisionNavigation.tryLocalChild z.Graph z.Focus.Id childIndex,
          z.Graph.SourceReadings.Ports.TryFind(z.Focus.Id, OccurrencePort.StructuralChild) with
    | Result.Ok child, Some port ->
        let step =
            { Parent = z.Focus.Id; Port = OccurrencePort.StructuralChild
              Ordinal = childIndex; Extent = port.Extent; Stamp = port.Stamp }
        createAt z.Graph child (step :: z.Path)
    | _ -> None

/// Move DOWN to the first child
let downFirst (z: PSGZipper) : PSGZipper option =
    down 0 z

/// Move LEFT to the previous sibling
let left (z: PSGZipper) : PSGZipper option =
    match z.Path with
    | [] -> None  // At root, no siblings
    | step :: restPath ->
        match z.Graph.SourceReadings.Ports.TryFind(step.Parent, step.Port) with
        | Some port when step.Ordinal > 0 ->
            port.Positions.TryFind(step.Ordinal - 1)
            |> Option.bind (fun child -> createAt z.Graph child ({ step with Ordinal = step.Ordinal - 1 } :: restPath))
        | _ -> None

/// Move RIGHT to the next sibling
let right (z: PSGZipper) : PSGZipper option =
    match z.Path with
    | [] -> None  // At root, no siblings
    | step :: restPath ->
        match z.Graph.SourceReadings.Ports.TryFind(step.Parent, step.Port) with
        | Some port when step.Ordinal + 1 < port.Extent ->
            port.Positions.TryFind(step.Ordinal + 1)
            |> Option.bind (fun child -> createAt z.Graph child ({ step with Ordinal = step.Ordinal + 1 } :: restPath))
        | _ -> None

/// Focus the one declared occurrence of a body; an ambiguous occurrence refuses.
let focusOn (nodeId: NodeId) (z: PSGZipper) : PSGZipper option =
    create z.Graph nodeId

// ═══════════════════════════════════════════════════════════════════════════
// FOCUS QUERIES
// ═══════════════════════════════════════════════════════════════════════════

/// Get the current focus node
let focus (z: PSGZipper) : SemanticNode = z.Focus

/// Get the focus node's ID
let focusId (z: PSGZipper) : NodeId = z.Focus.Id

/// Get the focus node's Kind
let focusKind (z: PSGZipper) : SemanticKind = z.Focus.Kind

/// Get the focus node's Type
let focusType (z: PSGZipper) : TypeIdentity = z.Focus.Type

/// Check if at root (no path)
let isAtRoot (z: PSGZipper) : bool = List.isEmpty z.Path

/// Get depth in tree (path length)
let depth (z: PSGZipper) : int = List.length z.Path

/// Get child count of focus
let childCount (z: PSGZipper) : int = List.length z.Focus.Children

/// Check if focus has children
let hasChildren (z: PSGZipper) : bool = not (List.isEmpty z.Focus.Children)

// ═══════════════════════════════════════════════════════════════════════════
// GRAPH LOOKUPS
// ═══════════════════════════════════════════════════════════════════════════

/// Get a node from the graph by ID
let getNode (nodeId: NodeId) (z: PSGZipper) : SemanticNode option =
    Revision.tryNode nodeId z.Graph

/// Get a node, failing if not found
let requireNode (nodeId: NodeId) (z: PSGZipper) : SemanticNode =
    match getNode nodeId z with
    | Some node -> node
    | None -> failwithf "Node %A not found in graph" nodeId

// ═══════════════════════════════════════════════════════════════════════════
// PATH INSPECTION
// ═══════════════════════════════════════════════════════════════════════════

/// Actual enclosing lambda occurrences, nearest first. Navigation retains a
/// shared node's current path rather than consulting its single Parent field.
let enclosingLambdas (z: PSGZipper) : SemanticNode list =
    z.Focus :: (z.Path |> List.choose (fun frame -> z.Graph.Nodes.TryFind frame.Parent))
    |> List.filter (fun node -> match node.Kind with SemanticKind.Lambda _ -> true | _ -> false)

let enclosingLambdaIds (z: PSGZipper) : NodeId list = enclosingLambdas z |> List.map _.Id

let findEnclosingLambda (z: PSGZipper) : SemanticNode option =
    enclosingLambdas z |> List.tryHead
