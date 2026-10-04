/// RecordWitness - Witness record construction and TStruct field access via XParsec
///
/// Leaf witness handling two node kinds:
/// 1. RecordExpr — construct a record from field values
/// 2. FieldGet on TStruct — extract a named field from a record
///
/// Must be registered BEFORE MemoryWitness so it intercepts TStruct FieldGets.
/// Non-TStruct FieldGets (strings, closures, DUs) return skip for MemoryWitness.
///
/// Codata-dependent: CPU → memref byte-offset ops, FPGA → hw.struct_* ops
module Alex.Witnesses.RecordWitness

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.NanopassArchitecture
open Alex.XParsec.PSGCombinators
open Alex.Patterns.RecordPatterns
module Components = Alex.Patterns.CallableAggregatePatterns

// ═══════════════════════════════════════════════════════════════════════════
// CATEGORY-SELECTIVE WITNESS (Private)
// ═══════════════════════════════════════════════════════════════════════════

let private witnessRecord (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    // Try RecordExpr first
    match tryMatch pRecordExpr ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
    | Some ((fields, copyFrom), _) ->
        // RecordExpr: field value nodes are already walked in post-order.
        // Recall each field value SSA from accumulator.
        let structTy = mapTypeAt node.Id ctx

        let componentRows = Components.hasRows ctx.Graph node.Id
        let dataFields = fields |> List.filter (fun (_, value) -> not (Components.inputIsCallable ctx.Graph node.Id value))
        let withComponents pattern =
            if componentRows then Components.pWithConstruction ctx node.Id pattern else pattern

        let fieldValues =
            dataFields |> List.choose (fun (fieldName, fieldNodeId) ->
                match MLIRAccumulator.recallNode fieldNodeId ctx.Accumulator with
                | Some (fieldSSA, fieldType) -> Some (fieldName, fieldSSA, fieldType)
                | None -> None)

        if fieldValues.Length <> dataFields.Length then
            WitnessOutput.error $"RecordExpr: Only {fieldValues.Length} of {dataFields.Length} field values witnessed"
        else
            match copyFrom with
            | Some origId ->
                // Copy-and-update: recall original record SSA, delegate to pBuildRecordCopyWith
                match MLIRAccumulator.recallNode origId ctx.Accumulator with
                | Some (origSSA, origTy) ->
                    let construction =
                        if componentRows then
                            pBuildRecordComponentCopy node.Id structTy { SSA = origSSA; Type = origTy } fieldValues (dataFields |> List.map snd)
                        else pBuildRecordCopyWith node.Id structTy origSSA fieldValues (dataFields |> List.map snd)
                    match tryMatchWithDiagnostics (withComponents construction) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                    | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                    | Result.Error diagnostic -> WitnessOutput.error $"RecordExpr copy-with: {diagnostic}"
                | None ->
                    WitnessOutput.error "RecordExpr copy-with: Original record not in accumulator"
            | None ->
                // Full construction: all field values provided
                match tryMatchWithDiagnostics (withComponents (pBuildRecord node.Id structTy fieldValues (dataFields |> List.map snd))) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                | Result.Error diagnostic -> WitnessOutput.error $"RecordExpr: {diagnostic}"

    | None ->
        // Try TupleExpr — tuples are first-class values on all platforms.
        // CPU: memref alloca + byte-offset stores via pBuildRecord
        // FPGA: hw.struct_create via pBuildRecord
        match node.Kind with
        | SemanticKind.TupleExpr elements ->
            // Map tuple type to TStruct with Item1, Item2, ... fields
            let structTy = mapTypeAt node.Id ctx

            // Recall each element's SSA from the accumulator (children already walked in post-order)
            let fieldValues =
                elements |> List.mapi (fun i elemId ->
                    let fieldName = sprintf "Item%d" (i + 1)
                    match MLIRAccumulator.recallNode elemId ctx.Accumulator with
                    | Some (ssa, ty) -> Some (fieldName, ssa, ty)
                    | None -> None)

            let resolved = fieldValues |> List.choose id
            if resolved.Length <> elements.Length then
                WitnessOutput.error $"TupleExpr: Only {resolved.Length} of {elements.Length} element values witnessed"
            else
                match tryMatchWithDiagnostics (pBuildRecord node.Id structTy resolved elements) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                | Result.Error diagnostic -> WitnessOutput.error $"TupleExpr: {diagnostic}"
        | _ ->

        // FieldSet on a TStruct record: r.Field <- v
        match node.Kind with
        | SemanticKind.FieldSet (structId, fieldName, _) when Components.hasRows ctx.Graph node.Id ->
            match tryMatchWithDiagnostics (Components.pAssignComponents ctx node.Id structId) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
            | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
            | Result.Error diagnostic -> WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "Record") (Some "callable assignment") $"RecordFieldSet '{fieldName}': {diagnostic}"
        | SemanticKind.FieldSet (structId, fieldName, valueId) ->
            match MLIRAccumulator.recallNode structId ctx.Accumulator, MLIRAccumulator.recallNode valueId ctx.Accumulator with
            | Some (structSSA, (TStruct _ as structTy)), Some (valueSSA, _) ->
                match tryMatchWithDiagnostics (pRecordFieldSet node.Id structSSA fieldName structTy valueSSA) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                | Result.Error diagnostic -> WitnessOutput.error $"RecordFieldSet '{fieldName}': {diagnostic}"
            | Some (_, structTy), Some _ ->
                WitnessOutput.error $"FieldSet '{fieldName}': target is not a record (type {structTy})"
            | None, _ -> WitnessOutput.error $"FieldSet '{fieldName}': record value not yet witnessed"
            | _, None -> WitnessOutput.error $"FieldSet '{fieldName}': value not yet witnessed"
        | _ ->

        // Try FieldGet on TStruct
        match tryMatch pFieldGet ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Some ((structId, _), _) when Components.hasRows ctx.Graph node.Id ->
            match tryMatchWithDiagnostics (Components.pReadComponent ctx node.Id structId) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
            | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
            | Result.Error diagnostic -> WitnessOutput.errorCoded AX4001 (Some node.Id) (Some "Record") (Some "callable projection") diagnostic
        | Some ((structId, fieldName), _) ->
            match MLIRAccumulator.recallNode structId ctx.Accumulator with
            | Some (structSSA, structTy) ->
                match structTy with
                | TStruct _ ->
                    // TStruct field access — handle here
                    match tryMatchWithDiagnostics (pRecordFieldGet node.Id structSSA fieldName structTy) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
                    | Result.Ok ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
                    | Result.Error diagnostic -> WitnessOutput.error $"RecordFieldGet: {diagnostic}"
                | _ ->
                    // Not TStruct — skip, let MemoryWitness handle (strings, closures, DUs)
                    WitnessOutput.skip
            | None ->
                // The operand's value decides the owner; without it no witness can
                // claim this FieldGet, so the missing operand is reported here.
                WitnessOutput.errorDiag (
                    Diagnostic.error (Some node.Id) (Some "Record") (Some "FieldGet")
                        $"FieldGet '{fieldName}' at node {NodeId.value node.Id}: struct operand node {NodeId.value structId} has not been witnessed")
        | None ->
            WitnessOutput.skip

// ═══════════════════════════════════════════════════════════════════════════
// NANOPASS REGISTRATION (Public)
// ═══════════════════════════════════════════════════════════════════════════

/// Record nanopass - witnesses RecordExpr and TStruct FieldGet nodes
let nanopass : Nanopass = {
    Name = "Record"
    Witness = witnessRecord
}
