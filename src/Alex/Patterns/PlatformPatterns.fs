/// Passive witnessing of source-published foreign declarations and calls.
/// Declaration identity, scope, ABI and adaptations belong to CCS/Baker.
module Alex.Patterns.PlatformPatterns

open Fidelity.PSG
open XParsec
open XParsec.Parsers
open XParsec.Combinators
open Alex.XParsec.PSGCombinators
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Elements.FuncElements


let private pBoundary : PSGParser<BoundaryEmissionProjection> =
    parser {
        let! state = getUserState
        return state.Graph.Emission.Boundary
    }

/// The source declaration is a leaf. Its import is witnessed at the published
/// module scope; its retained typechecking placeholder is not executable code.
let pBoundaryDeclaration : PSGParser<MLIROp list * TransferResult> =
    parser {
        let! node = getCurrentNode
        let! boundary = pBoundary
        do! ensure (boundary.DeclarationLeaves.Contains node.Id) "This occurrence has no published boundary declaration-leaf contract."
        return [], TRVoid
    }

/// Witness exactly the imports assigned to this source scope. No call inventory,
/// signature discovery, symbol reconciliation or declaration hoisting occurs here.
let boundaryImportsAt (scope: NodeId) (boundary: BoundaryEmissionProjection) : Result<MLIROp list, string> =
    let rec foreign ids =
        match ids with
        | [] -> Result.Ok []
        | id :: rest ->
            match boundary.Imports.TryFind id with
            | None -> Result.Error "Published import scope names an absent declaration."
            | Some declaration when declaration.Scope <> scope ->
                Result.Error "Published import has a different source owner scope."
            | Some declaration ->
                foreign rest |> Result.map (fun following -> publishedFuncDecl declaration :: following)
    foreign (boundary.ByScope.TryFind scope |> Option.defaultValue [])
    |> Result.map (fun declarations ->
        declarations @ (boundary.IntrinsicWriteImports.Values
                        |> Seq.filter (fun declaration -> declaration.Scope = scope)
                        |> Seq.map publishedIntrinsicWriteDecl |> Seq.toList))

let pBoundaryImports : PSGParser<MLIROp list> =
    parser {
        let! node = getCurrentNode
        let! boundary = pBoundary
        match boundaryImportsAt node.Id boundary with
        | Result.Ok declarations -> return declarations
        | Result.Error reason -> return! fail (Message reason)
    }

/// The source owns whether an adaptation exists and its exact operation.
/// SSA naming and checking physical correspondence are witness bookkeeping.
let private pBoundaryAdapt (consumer: NodeId) (operand: NodeId) (adaptation: Meet option) (value: Val) : PSGParser<MLIROp list * Val> =
    pPublishedAdapt consumer operand adaptation value

/// The source entry refers to one admitted import and one explicit loading
/// assumption. Its ABI is the import's; no ordinary lambda or code environment
/// is inferred from the retained typechecking declaration.
let private importedEntry (boundary: BoundaryEmissionProjection) formation =
    match boundary.Entries.TryFind formation, boundary.Loading with
    | Some entry, Some loading when entry.Formation = formation && entry.Loading = loading.Identity ->
        match boundary.Imports.TryFind entry.Import with
        | Some declaration when
            declaration.Binding = entry.Declaration
            && declaration.Library = loading.Contract.Library
            ->
            Result.Ok(entry, declaration)
        | _ -> Result.Error "Imported entry no longer has its exact declaration, import and loading contract."
    | _ -> Result.Error "Imported entry has no current source-published loading assumption."

let private importedFunctionType (declaration: BoundaryImport) =
    TFunc(
        declaration.Parameters |> List.map (snd >> boundaryScalarType),
        declaration.Result |> Option.map boundaryScalarType |> Option.toList
    )

/// Form a typed foreign code value only at its admitted formation occurrence.
/// Immutable aliases forward this actual SSA through existing BindingUses.
let pImportedFunctionAddress formation : PSGParser<MLIROp list * TransferResult> =
    parser {
        let! node = getCurrentNode
        let! boundary = pBoundary
        do! ensure (node.Id = formation) "Imported address must be witnessed at its actual formation."

        let! entry, declaration =
            match importedEntry boundary formation with
            | Result.Ok value -> preturn value
            | Result.Error reason -> fail (Message reason)

        do!
            ensure
                (match node.Kind with
                 | SemanticKind.Application(_, [ operand ]) -> operand = entry.Operand
                 | _ -> false)
                "Imported address differs from its declared extern operand."

        let! ssa = getNodeSSA formation

        let value =
            {
                SSA = ssa
                Type = importedFunctionType declaration
            }

        let! operation = pFuncConstant ssa declaration.Symbol value.Type
        return [ operation ], TRValue value
    }

/// Immutable byte borrowing is already established by Baker. Physical witnessing
/// shares the source descriptor; it neither allocates nor reconstructs its extent.
let pPublishedByteView : PSGParser<MLIROp list * TransferResult> = parser {
    let! node = getCurrentNode
    let! boundary = pBoundary
    match boundary.ByteViews.TryFind node.Id with
    | None -> return! fail (Message "Byte view lacks its source-published borrowing contract.")
    | Some view ->
        let! source, ty = pRecallNode view.Source
        let expected = TMemRef(TInt(IntWidth view.Representation.Bits))
        do! ensure (ty = expected) "Byte view source carrier disagrees with its published encoding representation."
        return [], TRValue { SSA = source; Type = expected }
}

/// The intrinsic has an explicit fd, bounded view and count. Every scalar
/// adaptation is the exact source meet; buffer bounds are not inferred here.
let pIntrinsicWrite : PSGParser<MLIROp list * TransferResult> = parser {
    let! node = getCurrentNode
    let! boundary = pBoundary
    match boundary.IntrinsicWrites.TryFind node.Id with
    | None -> return! fail (Message "Intrinsic write lacks its source-published contract.")
    | Some call ->
        match boundary.IntrinsicWriteImports.TryFind call.Import with
        | None -> return! fail (Message "Intrinsic write names an absent source-published declaration.")
        | Some declaration ->
            let! fdSSA, fdType = pRecallNode call.Fd
            let! fdOps, fd = pBoundaryAdapt node.Id call.Fd call.FdAdaptation { SSA = fdSSA; Type = fdType }
            let! bufferSSA, bufferType = pRecallNode call.Buffer
            let! countSSA, countType = pRecallNode call.Count
            let! countOps, count =
                if call.Count = call.Fd then parser {
                    do! ensure (call.CountAdaptation = call.FdAdaptation && countSSA = fdSSA && countType = fdType)
                            "Repeated intrinsic actual disagrees with its published meet or witnessed value."
                    return [], fd
                }
                else pBoundaryAdapt node.Id call.Count call.CountAdaptation { SSA = countSSA; Type = countType }
            let values = [fd; { SSA = bufferSSA; Type = bufferType }; count]
            do! ensure (List.map _.Type values = IntrinsicWriteAbi.parameters declaration)
                    "Intrinsic write operands disagree with the source-published ABI."
            let! resultSSA = getNodeSSA node.Id
            let raw = { SSA = resultSSA; Type = BoundaryAbi.scalarType declaration.Result }
            let! operation = pFuncCallResults [raw] declaration.Symbol values
            let! resultOps, result = pBoundaryAdapt node.Id node.Id call.ResultAdaptation raw
            return fdOps @ countOps @ [operation] @ resultOps, TRValue result
}

/// Witness a settled call. Missing publication is a refusal, never permission to
/// inspect a descriptor, infer marshalling from an MLIR type or create an import.
let pBoundaryCall : PSGParser<MLIROp list * TransferResult> =
    parser {
        let! node = getCurrentNode
        let! boundary = pBoundary
        match boundary.Calls.TryFind node.Id with
        | None -> return! fail (Message $"Boundary call {NodeId.value node.Id} has no source-published contract.")
        | Some call ->
            match boundary.Imports.TryFind call.Import with
            | None -> return! fail (Message "Published boundary call names an absent import.")
            | Some declaration ->
                let rec arguments (witnessed: Map<NodeId, Meet option * Val * Val>) (operands: BoundaryOperand list) : PSGParser<MLIROp list * Val list> = parser {
                    match operands with
                    | [] -> return [], []
                    | operand :: rest ->
                        let! ssa, ty = pRecallNode operand.Actual
                        let raw = { SSA = ssa; Type = ty }
                        let! operations, value =
                            match witnessed.TryFind operand.Actual with
                            | Some (adaptation, previous, value) -> parser {
                                do! ensure (adaptation = operand.Adaptation && previous = raw) "Repeated boundary actual disagrees with its witnessed source meet or value."
                                return [], value
                              }
                            | None -> pBoundaryAdapt node.Id operand.Actual operand.Adaptation raw
                        do! ensure (value.Type = boundaryScalarType operand.Abi) "Witnessed boundary argument disagrees with its published ABI."
                        // Repeated positions retain their order and reuse the
                        // one canonical meet definition for this actual.
                        let! remainingOps, values = arguments (witnessed.Add(operand.Actual, (operand.Adaptation, raw, value))) rest
                        return operations @ remainingOps, value :: values
                }
                let! argumentOps, values = arguments Map.empty call.Arguments
                let! results =
                    match call.Result with
                    | None -> preturn []
                    | Some ty -> parser {
                        let! resultSSA = getNodeSSA node.Id
                        return [{ SSA = resultSSA; Type = boundaryScalarType ty }]
                      }
                let! operation =
                    match call.Entry with
                    | None -> pFuncCallResults results declaration.Symbol values
                    | Some formation -> parser {
                        let! entry, imported =
                            match importedEntry boundary formation with
                            | Result.Ok value -> preturn value
                            | Result.Error reason -> fail (Message reason)
                        do! ensure (entry.Import = call.Import && imported = declaration &&
                                    entry.Transport.Contains call.Callee)
                                "Imported invocation differs from its source entry and pointer transport."
                        let! pointerSSA, pointerType = pRecallNode call.Callee
                        do! ensure (pointerType = importedFunctionType declaration &&
                                    pointerType = TFunc(List.map _.Type values, List.map _.Type results))
                                "Imported invocation pointer and operands disagree with its native ABI."
                        return! pFuncCallIndirectResults results pointerSSA values
                      }
                match results with
                | [] -> return argumentOps @ [operation], TRVoid
                | [value] ->
                    let! resultOps, result = pBoundaryAdapt node.Id node.Id call.ResultAdaptation value
                    return argumentOps @ [operation] @ resultOps, TRValue result
                | _ -> return! fail (Message "Scalar boundary publication has an invalid result list.")
    }
