/// Correspondence boundary between settled BAREWire storage and emitted MLIR.
/// Validates the final structured ops after middle-end passes, before serialization.
module Alex.Traversal.StaticStorageValidation

open Fidelity.PSG
open Alex.Dialects.Core.Types

let private flatten = OperationStructure.flatten

let validate (graph: Revision) (ops: MLIROp list) : Result<unit, string> =
    let all = flatten ops
    let pools = all |> List.choose (function MLIROp.GlobalBytePool (n,b,a,o) -> Some (n,b,a,o) | _ -> None)
    let projection = graph.Emission.Storage
    let errors = [
        match graph.StaticStringPool with
        | None -> if not pools.IsEmpty then yield "emitted a byte pool without a settled BAREWire plan"
        | Some pool ->
            let allocationAnchors = projection.LiteralPoolAnchors
            match pools with
            | [name, bytes, alignment, anchors] when name = pool.Symbol ->
                if bytes <> pool.Bytes || bytes.Length <> pool.Size then yield "emitted pool bytes/extent differ from the settled plan"
                if alignment <> pool.Alignment then yield "emitted pool alignment differs from the settled plan"
                if allocationAnchors |> List.exists (fun anchor -> not (List.contains anchor anchors)) then
                    yield "emitted pool lost its source allocation obligation anchor"
            | _ -> yield "expected exactly one allocation for the settled BAREWire string pool"
            let entries =
                pool.Entries |> List.collect (fun entry -> entry.NodeIds |> List.map (fun id -> id, entry)) |> Map.ofList
            for entry in pool.Entries do
                for id in entry.NodeIds do
                    let sourceSSA = Values.value id 0
                    let definitions = all |> List.choose (function
                        | MLIROp.MemRefOp (MemRefOp.GetGlobal (ssa, name, ty)) when ssa = sourceSSA -> Some (name, ty)
                        | _ -> None)
                    if definitions.IsEmpty || definitions |> List.exists (fun (name, _) -> name <> pool.Symbol) then
                        yield "source literal does not reference the settled pool allocation"
            let gets = all |> List.choose (function
                | MLIROp.MemRefOp (MemRefOp.GetGlobal (ssa, name, ty)) when name = pool.Symbol -> Some (ssa, ty)
                | _ -> None)
            if gets.IsEmpty then yield "settled pool has no emitted views"
            for get, actualType in gets do
                match get with
                | V (id, 0) ->
                    match entries.TryFind (NodeId id) with
                    | None -> yield "pool view has no corresponding source literal"
                    | Some entry ->
                        let s k = Values.value (NodeId id) k
                        let storage = TMemRefStatic(pool.Size, TInt(IntWidth 8))
                        let content = TMemRefStatic(entry.Length, TInt(IntWidth 8))
                        let dynamic = TMemRef(TInt(IntWidth 8))
                        if actualType <> storage then yield "pool get_global has the wrong allocation extent"
                        let offsets = all |> List.choose (function MLIROp.IndexOp (IndexOp.IndexConst (ssa, value)) when ssa = s 3 -> Some value | _ -> None)
                        if offsets.IsEmpty || offsets |> List.exists ((<>) (int64 entry.Offset)) then yield "literal byte offset differs from the settled plan"
                        let views = all |> List.choose (function MLIROp.MemRefOp (MemRefOp.View (ssa, src, off, fromTy, toTy)) when ssa = s 1 -> Some (src,off,fromTy,toTy) | _ -> None)
                        if views.IsEmpty || views |> List.exists ((<>) (s 0,s 3,storage,content)) then yield "literal view differs from the settled plan"
                        let casts = all |> List.choose (function MLIROp.MemRefOp (MemRefOp.Cast (ssa, src, fromTy, toTy)) when ssa = s 2 -> Some (src,fromTy,toTy) | _ -> None)
                        if casts.IsEmpty || casts |> List.exists ((<>) (s 1,content,dynamic)) then yield "literal cast lost its settled content view"
                | _ -> yield "pool get_global is not attached to a source literal"
    ]
    if List.isEmpty errors then Result.Ok ()
    else Result.Error ("BAREWire storage correspondence failed: " + String.concat "; " errors)

/// Compare the complete emitted writable inventory before a backend can place
/// it. This proves identity/type correspondence only, not linked-region fit.
let validateWritable arch (graph: Revision) (ops: MLIROp list) =
    let all = flatten ops
    let declarations = all |> List.choose (function MLIROp.GlobalMemref(name, ty, authority) -> Some(name, ty, authority) | _ -> None)
    let inventory = graph.Emission.Storage.ProgramStorage
    let (_, identities, declarationErrors, observed) =
        declarations
        |> List.fold (fun (names, identities, errors, observed) (name, ty, authority) ->
            let duplicate =
                if Set.contains name names then ["duplicate writable declaration: " + name] else []
            match authority with
            | None ->
                Set.add name names, identities,
                (duplicate @ ["writable declaration lacks source allocation authority: " + name]) :: errors, observed
            | Some entry ->
                let correspondence =
                    if inventory.Entries.TryFind entry.Identity <> Some entry then
                        Some("writable declaration carries a stale or foreign inventory entry: " + name)
                    elif Alex.Patterns.MemoryPatterns.programStorageType arch graph entry <> Some ty then
                        Some("writable declaration type disagrees with source storage: " + name)
                    else None
                let reads = all |> List.choose (function
                    | MLIROp.MemRefOp(MemRefOp.GetGlobal(_, symbol, actual)) when symbol = name -> Some actual
                    | _ -> None)
                let localErrors = [
                    yield! duplicate
                    if Set.contains entry.Identity identities then
                        yield sprintf "source storage %A was emitted more than once" entry.Identity
                    yield! Option.toList correspondence
                    if reads.IsEmpty || reads |> List.exists ((<>) ty) then
                        yield "writable allocation views disagree with its declaration: " + name
                ]
                Set.add name names, Set.add entry.Identity identities, localErrors :: errors,
                (if correspondence.IsNone then (name, entry) :: observed else observed)
        ) (Set.empty, Set.empty, [], [])
    let errors = [
        for KeyValue(_, reason) in inventory.Unresolved do yield reason
        yield! declarationErrors |> List.rev |> List.concat
        for KeyValue(identity, _) in inventory.Entries do
            if not (Set.contains identity identities) then
                yield sprintf "source writable allocation %A has no emitted declaration" identity
    ]
    if List.isEmpty errors then Ok(List.rev observed)
    else Error("Writable storage correspondence failed: " + String.concat "; " errors)
