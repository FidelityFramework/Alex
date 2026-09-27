// Measures, for one published revision, what the entire edge set says about the
// units of witnessing: the starts the traversal uses today, the region under each
// start, the edges that cross between regions, and the groups of regions that no
// crossing edge connects.
//
// This is a measurement. It changes nothing in Alex and decides nothing. It reads
// a revision through the contract only.
//
// Usage, from a script that holds a revision:
//   #load "PlanMeasure.fsx"
//   PlanMeasure.report "name" revision

#if !PLAN_MEASURE_REFERENCED
#r "../../Fidelity.PSG/src/Fidelity.PSG/bin/Debug/net10.0/Fidelity.PSG.dll"
#endif

open Fidelity.PSG

/// The starts in the order the traversal visits them today
/// (Traversal/NanopassArchitecture.fs, runAllNanopasses).
let starts (revision: Revision) : NodeId list =
    let boundary = revision.Emission.Boundary
    let spatial = revision.Emission.Spatial
    let boundaryScopes =
        Set.union (boundary.ByScope |> Map.toList |> List.map fst |> Set.ofList)
                  (boundary.IntrinsicWriteImports |> Map.toList |> List.map (fun (_, row) -> row.Scope) |> Set.ofList)
    let sourceRoots =
        Set.unionMany [ boundaryScopes; spatial.ByScope |> Map.toList |> List.map fst |> Set.ofList; spatial.Required; spatial.CodeRoots ]
    let ordered =
        Set.toList spatial.CodeRoots
        @ (revision.DeclarationRoots |> List.map fst)
        @ (revision.ModuleClassifications |> Map.toList |> List.collect (fun (moduleId, row) -> row.Definitions @ [ moduleId ]))
        @ Set.toList sourceRoots
    ordered
    |> List.distinct
    |> List.filter (fun id ->
        match revision.Nodes.TryFind id with
        | Some node -> node.IsReachable || sourceRoots.Contains id
        | None -> false)

/// The region of each start: the reachable nodes under it by containment. A node
/// under more than one start belongs to the first, as the visited set decides today.
let regions (revision: Revision) (ordered: NodeId list) : Map<NodeId, NodeId> =
    let rec claim (start: NodeId) (owner: Map<NodeId, NodeId>) (pending: NodeId list) : Map<NodeId, NodeId> =
        match pending with
        | [] -> owner
        | current :: rest ->
            if owner.ContainsKey current then claim start owner rest
            else
                match revision.Nodes.TryFind current with
                | Some node when node.IsReachable || current = start ->
                    claim start (owner.Add(current, start)) (node.Children @ rest)
                | _ -> claim start owner rest
    ordered |> List.fold (fun owner start -> claim start owner [ start ]) Map.empty

/// The groups of regions that the crossing edges given connect.
let groups (ordered: NodeId list) (crossing: (NodeId * NodeId) list) : NodeId list list =
    let rec root (parent: Map<NodeId, NodeId>) (id: NodeId) : NodeId =
        match parent.TryFind id with
        | Some above when above <> id -> root parent above
        | _ -> id
    let joined =
        crossing |> List.fold (fun (parent: Map<NodeId, NodeId>) (left, right) ->
            let a, b = root parent left, root parent right
            if a = b then parent else parent.Add(max a b, min a b)) Map.empty
    ordered |> List.groupBy (root joined) |> List.map snd

let private caseName (value: obj) =
    let text = sprintf "%A" value
    let cut = text.IndexOfAny [| ' '; '('; '\n' |]
    if cut < 0 then text else text.Substring(0, cut)

let report (name: string) (revision: Revision) =
    let ordered = starts revision
    let owner = regions revision ordered
    let reachable = revision.Nodes |> Map.filter (fun _ node -> node.IsReachable) |> Map.count
    let sizes = owner |> Map.toList |> List.countBy snd |> Map.ofList
    // An edge crosses when its ends lie in the regions of different starts.
    let crossings =
        revision.Edges |> List.collect (fun edge ->
            match owner.TryFind edge.Target with
            | None -> []
            | Some target ->
                edge.Sources |> List.choose (fun source ->
                    match owner.TryFind source with
                    | Some from when from <> target -> Some (edge, source, from, target)
                    | _ -> None))
    let unowned =
        revision.Nodes |> Map.filter (fun id node -> node.IsReachable && not (owner.ContainsKey id)) |> Map.count
    printfn "== %s" name
    printfn "   nodes %d, reachable %d, edges %d" revision.Nodes.Count reachable revision.Edges.Length
    printfn "   starts %d, reachable nodes under no start %d" ordered.Length unowned
    printfn "   region sizes: %A" (ordered |> List.map (fun start -> NodeId.value start, (sizes.TryFind start |> Option.defaultValue 0)) |> List.sortByDescending snd |> List.truncate 12)
    printfn "   crossing edge ends: %d" crossings.Length
    crossings |> List.countBy (fun (edge, _, _, _) -> caseName edge.Class + "/" + caseName edge.Role) |> List.sortByDescending snd
    |> List.iter (fun (kind, count) -> printfn "      %-44s %d" kind count)
    // Rule 1: every crossing edge connects two regions.
    let every = crossings |> List.map (fun (_, _, from, target) -> from, target)
    // Rule 2: a reference whose source or target is a start itself does not connect.
    // The reference names a declaration, and a declaration is reached by its symbol.
    let interior =
        crossings |> List.filter (fun (edge, source, _, _) ->
            not (edge.Class = EdgeClass.Reference && (List.contains edge.Target ordered || List.contains source ordered)))
        |> List.map (fun (_, _, from, target) -> from, target)
    let byEvery, byInterior = groups ordered every, groups ordered interior
    printfn "   rule 1, every crossing edge connects: %d groups, largest %d starts" byEvery.Length (byEvery |> List.map List.length |> List.max)
    printfn "   rule 2, references to a start do not connect: %d groups, largest %d starts" byInterior.Length (byInterior |> List.map List.length |> List.max)
