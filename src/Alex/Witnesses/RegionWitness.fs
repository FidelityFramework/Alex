/// Region creation, allocation, release and copy occurrences named by
/// Codata.RegionAllocations and Codata.RegionCopyEndpoints. The rows publish
/// extent, capacity, alignment, lifetime and release incidence. They publish no
/// storage operation: no residence for the region, no byte offset for a value
/// allocated in it and no copy operation. An occurrence without a published
/// memory operation is refused here by its row. It is not dispatched by
/// intrinsic module to another storage Pattern, and no placement, offset or
/// destination allocation is chosen. An occurrence that has a published
/// memory operation is left to the witness of that operation.
module Alex.Witnesses.RegionWitness

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture

let private refuse (node: SemanticNode) phase message =
    WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "Region") (Some phase) message

let private allocationOf (codata: Codata) (occurrence: NodeId) =
    codata.RegionAllocations |> Map.tryPick (fun _ row ->
        if List.contains occurrence row.AllocatedValues then Some row else None)

let private releaseOf (codata: Codata) (occurrence: NodeId) =
    codata.RegionAllocations |> Map.tryPick (fun _ row ->
        if row.ScopeExitReleases |> List.exists (fun (_, release) -> release = occurrence) then Some row else None)

let private witness (ctx: WitnessContext) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Application _ ->
        let codata = ctx.Graph.Codata
        let memory = ctx.Graph.Emission.Memory
        let site = NodeId.value node.Id
        if memory.Operations.ContainsKey node.Id || memory.ArrayCopies.ContainsKey node.Id then WitnessOutput.skip
        else
        match codata.RegionCopyEndpoints.TryFind node.Id, codata.RegionAllocations.TryFind node.Id,
              allocationOf codata node.Id, releaseOf codata node.Id with
        | Some copy, _, _, _ ->
            let kind = match copy.Kind with RegionCopyKind.CopyOut -> "copyOut" | RegionCopyKind.CopyTo -> "copyTo"
            refuse node "copy endpoint"
                (sprintf "Region copy endpoint %d (%s): Codata.RegionCopyEndpoints publishes a %d-byte source extent and destination storage %d, and the revision publishes no copy operation for it (no Emission.Memory.ArrayCopies or Emission.Memory.Operations row at node %d). Alex does not choose the destination allocation."
                    site kind copy.SourceByteExtent (NodeId.value copy.DestinationStorage) site)
        | None, Some row, _, _ ->
            refuse node "creation"
                (sprintf "Region creation %d: Codata.RegionAllocations publishes a capacity of %d bytes at alignment %d, and the revision publishes no storage operation for the region (no Emission.Memory.Operations row at node %d). Alex does not choose a residence or placement for region storage."
                    site row.Capacity row.Alignment site)
        | None, None, Some row, _ ->
            refuse node "allocation"
                (sprintf "Region allocation %d in region %d: the revision publishes no byte offset for this value within the region's %d-byte extent (no Emission.Memory.Operations row at node %d). Alex does not compute allocation offsets."
                    site (NodeId.value row.Region) row.ByteExtent site)
        | None, None, None, Some row ->
            refuse node "release"
                (sprintf "Region release %d of region %d: the revision publishes no storage operation for the region it releases (no Emission.Memory.Operations row at node %d)."
                    site (NodeId.value row.Region) site)
        | None, None, None, None -> WitnessOutput.skip
    | _ -> WitnessOutput.skip

let nanopass : Nanopass = { Name = "Region"; Witness = witness }
