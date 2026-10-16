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
    let publishedDeclaration (declaration: BoundaryImport) =
        let resourceCarrier = function BoundaryScalar.ResourceHandle _ -> true | _ -> false
        if (declaration.Parameters |> List.exists (snd >> resourceCarrier))
           || (declaration.Result |> Option.exists resourceCarrier) then
            // The current source import remains the authority. Its resource
            // signature has no portable scalar spelling or generic-call route.
            ResourceImport declaration
        else publishedFuncDeclIn boundary declaration
    let rec foreign ids =
        match ids with
        | [] -> Result.Ok []
        | id :: rest ->
            match boundary.Imports.TryFind id with
            | None -> Result.Error "Published import scope names an absent declaration."
            | Some declaration when declaration.Scope <> scope ->
                Result.Error "Published import has a different source owner scope."
            | Some declaration ->
                foreign rest |> Result.map (fun following -> publishedDeclaration declaration :: following)
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

/// The source owns the conditional result relation. Retain its exact current
/// application and citizens without evaluating the relation or choosing a width.
let private pWritableResult (call: BoundaryCall) (imported: BoundaryImport) : PSGParser<unit> = parser {
    match call.Result with
    | None ->
        do! ensure call.ResultAdaptation.IsNone "Void writable call has a scalar result adaptation."
    | Some(BoundaryScalar.Integer(64, true)) ->
        let! state = getUserState
        let graph = state.Graph
        let! account =
            match graph.Emission.Numeric.ForeignResultUses |> List.filter (fun useRow ->
                useRow.Application.Call = call.Site && useRow.Application.Declaration = imported.Binding) with
            | [account] -> preturn account
            | _ -> fail (Message "Writable signed result lacks its unique current same-call foreign-result account.")
        do! ensure
                ((account.Application.Hypothesis |> Option.exists (fun hypothesis -> hypothesis.Declaration = imported.Binding))
                 && (account.Application.Arguments |> List.map (fun argument -> argument.Index, argument.Node))
                    = (call.Arguments |> List.mapi (fun index argument -> index, argument.Actual)))
                "Writable signed result differs from its declared hypothesis or ordered actuals."
        let! participants =
            match account.Participants with
            | ParticipantEvidence.Established participants -> preturn participants
            | ParticipantEvidence.Pending _ -> fail (Message "Writable signed result has pending source participants.")
        let! claims =
            match account.Claims with
            | [(ForeignResultProofRole.LogicalCoverage, logical); (ForeignResultProofRole.AbiNarrowing, abi)] when logical <> abi ->
                preturn [ForeignResultProofRole.LogicalCoverage, logical; ForeignResultProofRole.AbiNarrowing, abi]
            | _ -> fail (Message "Writable signed result lacks its distinct logical/ABI claim citizens.")
        let currentClaim (role, citizen) =
            match graph.CurrentClaims.TryFind citizen, graph.ObligationSources.TryFind citizen with
            | Some claim, Some [sources] ->
                List.contains claim graph.Obligations && sources = (participants |> List.map _.Node)
                && (match claim.Body with
                    | ObligationBody.ForeignResultCoverage model -> model.Application = account.Application && model.Role = role
                    | _ -> false)
                && (graph.Emission.Boundary.WritableBufferUses.Values
                    |> Seq.filter (fun useRow -> useRow.Call = call.Site)
                    |> Seq.forall (fun useRow ->
                        useRow.Participants.Contains citizen
                        && (sources |> List.forall useRow.Participants.Contains)
                        && (participants |> List.forall (fun participant -> useRow.Participants.Contains participant.Node))))
            | _ -> false
        do! ensure (claims |> List.forall currentClaim)
                "Writable signed result lacks its current required logical/ABI claims and source support."
    | Some _ -> return! fail (Message "Writable byte calls support only void or the declared signed64 result.")
}

/// Consume the current per-use account. Bounds and foreign effects were settled
/// by Baker; this reader only retains their exact operand and claim incidence.
let private pWritableOperand (call: BoundaryCall) (imported: BoundaryImport) ordinal (operand: BoundaryOperand) identity : PSGParser<unit> = parser {
    let! state = getUserState
    let graph = state.Graph
    let boundary = graph.Emission.Boundary
    let! declaration, useRow =
        match boundary.WritableBufferDeclarations.TryFind identity, boundary.WritableBufferUses.TryFind(call.Site, ordinal) with
        | Some declaration, Some row when declaration.Identity = identity && row.Declaration = identity -> preturn(declaration, row)
        | _ -> fail (Message "Writable boundary operand lacks its exact current declaration and per-use account.")
    do! ensure
            (call.Entry.IsNone && call.Resource.IsNone && call.Result = imported.Result
             && call.Site = useRow.Call && useRow.Parameter = ordinal && declaration.Parameter = ordinal
             && useRow.CountParameter = declaration.CountParameter && imported.Identity = declaration.Descriptor
             && imported.Binding = declaration.Declaration && operand.Formal = declaration.BufferFormal
             && operand.Actual = useRow.Buffer && operand.Adaptation.IsNone
             && imported.Parameters = (call.Arguments |> List.map (fun actual -> actual.Formal, actual.Abi))
             && (call.Arguments |> List.tryItem useRow.CountParameter |> Option.exists (fun count ->
                 count.Actual = useRow.Count && count.Formal = declaration.CountFormal)))
            "Writable boundary operand differs from its exact direct call, native ordinal or ordered actuals."
    do! ensure
            ((graph.Emission.Memory.Operations.TryFind useRow.Allocation |> Option.exists (function
                | MemoryWitnessOperation.ArrayAllocation allocation -> allocation.Site = useRow.Allocation
                | _ -> false))
             && (graph.Emission.Numeric.Elements.TryFind useRow.Buffer |> Option.exists (function
                 | SettledSlot.Integer(8, Some _) -> true
                 | _ -> false)))
            "Writable boundary operand lacks its current allocation and exact byte-format account."
    let currentClaim citizen kind =
        match graph.CurrentClaims.TryFind citizen, graph.ObligationSources.TryFind citizen with
        | Some claim, Some [sources] ->
            claim.Kind = kind && List.contains claim graph.Obligations && List.tryHead sources = Some call.Site
            && ([identity;useRow.Buffer;useRow.Count;useRow.Allocation;useRow.Capacity;useRow.ByteFormat]
                |> List.forall (fun id -> List.contains id sources))
        | _ -> false
    do! ensure
            (currentClaim useRow.CountCoverage "foreign-writable-buffer-count"
             && currentClaim useRow.StorageCoverage "foreign-writable-buffer-storage"
             && ([call.Site;identity;useRow.Buffer;useRow.Count;useRow.Allocation;useRow.Capacity;useRow.ByteFormat;useRow.CountCoverage;useRow.StorageCoverage]
                 |> List.forall useRow.Participants.Contains))
            "Writable boundary operand lacks its current required count/storage claim citizens and support."
    return ()
}

/// Read the source-owned lineage; neither a matching type nor participant
/// membership can create a resource access. Selection semantics remain with
/// the published account and its current conversion/cleanup proof premises.
let internal resourceAccessAt boundary site source kind =
    BoundaryAbi.resourceAccessAt boundary site source kind

let internal pResourceAlias site sourceId (source: Val) : PSGParser<MLIROp list * TransferResult> = parser {
    let! state = getUserState
    let! _ =
        match resourceAccessAt state.Graph.Emission.Boundary site sourceId BoundaryResourceAccessKind.ImmutableAlias with
        | Ok rows -> preturn rows
        | Result.Error reason -> fail (Message reason)
    do! ensure
            (source.Type = Alex.CodeGeneration.TypeMapping.valueTypeAt state.Graph site
             && (match source.Type with TOpaqueHandle _ | TResourceOption _ -> true | _ -> false))
            "Immutable resource alias differs from its exact source representation."
    return [ResourceAlias(site, source)], TRValue source
}

let private pResourceCall (call: BoundaryCall) (imported: BoundaryImport) : PSGParser<MLIROp list * TransferResult> = parser {
    let! state = getUserState
    let boundary = state.Graph.Emission.Boundary
    do! ensure (call.Entry.IsNone) "Resource calls require their exact direct source invocation."
    do! ensure (call.ResultAdaptation.IsNone) "Resource conversion cannot be replaced by a numeric result adaptation."
    let! resource =
        match call.Resource with
        | Some(BoundaryResourceUse.AcquireNullable acquisition) -> preturn acquisition.Declaration
        | Some(BoundaryResourceUse.ReleaseOwned release) -> preturn release.Declaration
        | None -> fail (Message "Resource call lacks its source conversion and cleanup account.")
    let! declaration =
        match boundary.ResourceDeclarations.TryFind resource with
        | Some declaration when declaration.Identity = resource -> preturn declaration
        | _ -> fail (Message "Resource call has no exact current resource declaration.")
    match call.Resource with
    | Some(BoundaryResourceUse.AcquireNullable _) ->
        do! ensure
                (imported.Binding = declaration.Acquisition
                 && imported.Result = Some(BoundaryScalar.ResourceHandle(resource, true))
                 && call.Result = imported.Result)
                "Nullable resource acquisition differs from its declared native result."
        let rec arguments witnessed = function
            | [] -> preturn ([], [])
            | (operand: BoundaryOperand) :: rest -> parser {
                do! ensure
                        (match operand.Abi with BoundaryScalar.Integer _ | BoundaryScalar.Boolean -> true | _ -> false)
                        "Resource acquisition does not admit nested resource or callable native actuals."
                let! ssa, ty = pRecallNode operand.Actual
                let raw = { SSA = ssa; Type = ty }
                let! operations, value =
                    match Map.tryFind operand.Actual witnessed with
                    | Some(adaptation, previous, value) -> parser {
                        do! ensure (adaptation = operand.Adaptation && previous = raw)
                                "Repeated resource actual disagrees with its source meet or witnessed value."
                        return [], value
                      }
                    | None -> pBoundaryAdapt call.Site operand.Actual operand.Adaptation raw
                do! ensure (value.Type = BoundaryAbi.scalarType operand.Abi)
                        "Resource acquisition actual differs from its source-published native ABI."
                let! remaining, values = arguments (Map.add operand.Actual (operand.Adaptation, raw, value) witnessed) rest
                return operations @ remaining, value :: values
              }
        let! argumentOps, values = arguments Map.empty call.Arguments
        let resultType = Alex.CodeGeneration.TypeMapping.valueTypeAt state.Graph call.Site
        do! ensure
                (match resultType with TResourceOption _ -> true | _ -> false)
                "Nullable resource acquisition lacks its source-settled opaque Option representation."
        let! ssa = getNodeSSA call.Site
        let result = { SSA = ssa; Type = resultType }
        return argumentOps @ [ResourceCall(call.Site, values, Some result)], TRValue result
    | Some(BoundaryResourceUse.ReleaseOwned release) ->
        do! ensure
                (imported.Binding = declaration.Release && imported.Result.IsNone && call.Result.IsNone)
                "Owned resource release differs from its exact unary void declaration."
        let! operand =
            match call.Arguments with
            | [operand] when operand.Abi = BoundaryScalar.ResourceHandle(resource, false) && operand.Adaptation.IsNone -> preturn operand
            | _ -> fail (Message "Owned resource release lacks its exact nonnull actual at native ordinal zero.")
        match boundary.Calls.TryFind release.Acquisition with
        | Some original ->
            do! ensure
                    (match original.Resource with
                     | Some(BoundaryResourceUse.AcquireNullable acquisition) ->
                         acquisition.Declaration = resource && acquisition.Cleanup = release.Cleanup
                     | _ -> false)
                    "Owned resource release differs from its original acquisition and cleanup account."
        | None -> return! fail (Message "Owned resource release has no current source-published acquisition.")
        let! ssa, ty = pRecallNode operand.Actual
        let expected = Alex.CodeGeneration.TypeMapping.valueTypeAt state.Graph operand.Actual
        do! ensure
                (ty = expected
                 && (match expected with
                     | TOpaqueHandle(handleType, bits, alignment) ->
                         handleType = declaration.HandleType && bits = declaration.PointerBits && alignment > 0
                     | _ -> false))
                "Owned resource release actual lacks its exact source-settled opaque handle representation."
        return [ResourceCall(call.Site, [{ SSA = ssa; Type = ty }], None)], TRVoid
    | None -> return! fail (Message "Resource call lacks its source conversion and cleanup account.")
}

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

let private importedFunctionType boundary (declaration: BoundaryImport) =
    TFunc(
        BoundaryAbi.parametersIn boundary declaration,
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

        do! ensure
                (declaration.Parameters |> List.forall (fun (_, scalar) -> match scalar with BoundaryScalar.WritableBytes _ -> false | _ -> true))
                "Writable byte declarations require a direct source call, not a function address."

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
                Type = importedFunctionType boundary declaration
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
        | Some call when call.Arguments |> List.exists (fun operand -> operand.OptionalEntry.IsSome) ->
            return! fail (Message "Optional native-entry boundary conversion requires target-pathway authority; this consumer does not admit it.")
        | Some call ->
            match boundary.Imports.TryFind call.Import with
            | None -> return! fail (Message "Published boundary call names an absent import.")
            | Some declaration when call.Resource.IsSome -> return! pResourceCall call declaration
            | Some declaration when
                (List.map snd declaration.Parameters @ Option.toList declaration.Result)
                |> List.exists (function BoundaryScalar.ResourceHandle _ -> true | _ -> false) ->
                return! fail (Message "Resource call lacks its source conversion and cleanup account.")
            | Some declaration ->
                let writable = declaration.Parameters |> List.exists (fun (_, scalar) -> match scalar with BoundaryScalar.WritableBytes _ -> true | _ -> false)
                do!
                    if writable then
                        parser {
                            do! ensure
                                    (call.Entry.IsNone && call.Result = declaration.Result
                                     && declaration.Parameters = (call.Arguments |> List.map (fun actual -> actual.Formal, actual.Abi)))
                                    "Writable byte calls require their exact direct signature and complete ordered actuals."
                            return! pWritableResult call declaration
                        }
                    else preturn ()
                let rec arguments ordinal (witnessed: Map<NodeId, Meet option * Val * Val>) (operands: BoundaryOperand list) : PSGParser<MLIROp list * Val list> = parser {
                    match operands with
                    | [] -> return [], []
                    | operand :: rest ->
                        do!
                            match operand.Abi with
                            | BoundaryScalar.WritableBytes identity -> pWritableOperand call declaration ordinal operand identity
                            | _ -> preturn ()
                        let! ssa, ty = pRecallNode operand.Actual
                        let raw = { SSA = ssa; Type = ty }
                        let! operations, value =
                            match witnessed.TryFind operand.Actual with
                            | Some (adaptation, previous, value) -> parser {
                                do! ensure (adaptation = operand.Adaptation && previous = raw) "Repeated boundary actual disagrees with its witnessed source meet or value."
                                return [], value
                              }
                            | None -> pBoundaryAdapt node.Id operand.Actual operand.Adaptation raw
                        do! ensure (value.Type = BoundaryAbi.scalarTypeIn boundary operand.Abi) "Witnessed boundary argument disagrees with its published ABI."
                        // Repeated positions retain their order and reuse the
                        // one canonical meet definition for this actual.
                        let! remainingOps, values = arguments (ordinal + 1) (witnessed.Add(operand.Actual, (operand.Adaptation, raw, value))) rest
                        return operations @ remainingOps, value :: values
                }
                let! argumentOps, values = arguments 0 Map.empty call.Arguments
                let! results =
                    match call.Result with
                    | None -> preturn []
                    | Some ty -> parser {
                        let! resultSSA = getNodeSSA node.Id
                        return [{ SSA = resultSSA; Type = boundaryScalarType ty }]
                      }
                let! operation =
                    match call.Arguments |> List.exists (fun operand -> match operand.Abi with BoundaryScalar.WritableBytes _ -> true | _ -> false), call.Entry with
                    | true, None -> preturn (WritableBufferCall(call.Site, values, List.tryHead results))
                    | true, Some _ -> fail (Message "Writable byte calls require their exact direct source invocation.")
                    | false, None -> pFuncCallResults results declaration.Symbol values
                    | false, Some formation -> parser {
                        let! entry, imported =
                            match importedEntry boundary formation with
                            | Result.Ok value -> preturn value
                            | Result.Error reason -> fail (Message reason)
                        do! ensure (entry.Import = call.Import && imported = declaration &&
                                    entry.Transport.Contains call.Callee)
                                "Imported invocation differs from its source entry and pointer transport."
                        let! pointerSSA, pointerType = pRecallNode call.Callee
                        do! ensure (pointerType = importedFunctionType boundary declaration &&
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
