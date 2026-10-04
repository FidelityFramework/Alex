/// Passive transport of source-settled callable components in records and unions.
/// Only the published selector and environment views enter aggregate data storage.
module Alex.Patterns.CallableAggregatePatterns

open Fidelity.PSG
open XParsec
open XParsec.Parsers
open XParsec.Combinators
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.XParsec.PSGCombinators
open Alex.CodeGeneration.TypeMapping
open Alex.Elements.MLIRAtomics
open Alex.Elements.ArithElements
open Alex.Elements.FuncElements
open Alex.Elements.SCFElements
open Alex.Elements.MemRefElements
module Values = Alex.Traversal.Values
module Operands = Alex.Traversal.CallableOperands

let hasRows (graph: Revision) occurrence = graph.Emission.Callable.AggregateValues.ContainsKey occurrence

/// This is a published slot lookup, not field-type inference.
let inputIsCallable (graph: Revision) occurrence value =
    graph.Emission.Callable.AggregateValues.TryFind occurrence
    |> Option.exists (List.exists (fun row ->
        row.Value = Some value &&
        (graph.Emission.Callable.AggregateSlots.TryFind row.Slot
         |> Option.exists (fun slot -> match slot.Path with [_] -> true | _ -> false))))

let private pRows occurrence = parser {
    let! state = getUserState
    do! ensure (state.Current.Id = occurrence && state.Zipper.Focus.Id = occurrence)
            "Callable aggregate transport requires its actual Huet occurrence."
    let projection = state.Graph.Emission.Callable
    let! rows, account =
        match projection.AggregateValues.TryFind occurrence, projection.AggregateDependencies.TryFind occurrence with
        | Some rows, Some account when not rows.IsEmpty && account.Occurrence = occurrence &&
                                      (account.Values |> List.filter (fun row -> row.Occurrence = occurrence)) = rows ->
            preturn (rows, account)
        | _ -> fail (Message "Callable aggregate transport lacks its current published dependency account.")
    do! ensure (rows |> List.forall (fun row -> row.Occurrence = occurrence))
            "Callable aggregate row names another occurrence."
    do! ensure (account.Slots |> List.forall (fun slot -> projection.AggregateSlots.TryFind slot.Identity = Some slot))
            "Callable aggregate dependency account has a changed slot."
    do! ensure (account.Carriers |> List.forall (fun carrier -> projection.Carriers.TryFind carrier.Occurrence = Some carrier))
            "Callable aggregate dependency account has a changed formation."
    do! ensure (account.Contracts |> List.forall (fun contract -> projection.Contracts.TryFind contract.Identity = Some contract))
            "Callable aggregate dependency account has a changed receiving contract."
    return rows
}

let private pAlternative (row: CallableAggregateValue) (alternative: CallableAggregateAlternative) = parser {
    let! state = getUserState
    let projection = state.Graph.Emission.Callable
    let! slot =
        match projection.AggregateSlots.TryFind row.Slot with
        | Some slot -> preturn slot
        | None -> fail (Message "Callable aggregate transport lacks its resolved slot.")
    let! carrier =
        match projection.Carriers.TryFind alternative.Carrier with
        | Some carrier when carrier.Formation = alternative.Formation &&
                            carrier.EnvironmentValue = alternative.EnvironmentValue &&
                            carrier.Contract = slot.Contract && slot.Contract = Result.Ok alternative.Contract -> preturn carrier
        | _ -> fail (Message "Callable aggregate alternative lost its paired formation, environment or contract.")
    do! ensure (carrier.Kind = CallableKind.OrdinaryFlatClosure)
            "Native callable aggregate realization requires its published native entry contract."
    do! ensure alternative.Adapter.IsNone
            "Callable aggregate adapters must be represented as settled callable carriers before witnessing."
    let! contract =
        match slot.Contract |> Result.toOption |> Option.bind projection.Contracts.TryFind with
        | Some contract when contract.Kind = carrier.Kind -> preturn contract
        | _ -> fail (Message "Callable aggregate alternative lacks its receiving contract.")
    do! ensure (carrier.EnvironmentValue.IsSome = alternative.EnvironmentPlacement.IsSome &&
                carrier.Environment.IsSome = alternative.EnvironmentPlacement.IsSome)
            "Callable aggregate alternative lost its explicit environment presence."
    do! ensure (alternative.EnvironmentPlacement |> Option.forall (fun placement ->
        Some placement.Value = carrier.EnvironmentValue &&
        (carrier.Environment |> Option.exists (fun environment -> environment.Owner = placement.Owner)) &&
        contract.EnvironmentBytes = Some placement.ViewBytes && placement.Adaptation.IsNone))
            "Callable aggregate environment view lacks its exact source-owned convention."
    return carrier
}

let private pSelector (row: CallableAggregateValue) = parser {
    let! selector =
        match row.Selector with
        | Some selector when selector.Lower = 0 && selector.UpperExclusive = row.Alternatives.Length &&
                             (row.Alternatives |> List.map _.Ordinal) = [0 .. row.Alternatives.Length - 1] -> preturn selector
        | _ -> fail (Message "Callable aggregate selector has no exact alternative domain.")
    match selector.Storage, selector.Slot, selector.ByteOffset with
    | None, None, None when row.Alternatives.Length = 1 -> return None
    | Some _, Some(SettledSlot.Integer _ as slot), Some offset when offset >= 0 ->
        match settledScalarType slot with
        | Some ty -> return Some(offset, ty)
        | None -> return! fail (Message "Callable aggregate selector has no published integer carrier.")
    | _ -> return! fail (Message "Callable aggregate selector has no complete source placement.")
}

let private pReceivingType (row: CallableAggregateValue) = parser {
    let! state = getUserState
    let projection = state.Graph.Emission.Callable
    let! contract =
        match projection.AggregateSlots.TryFind row.Slot with
        | Some slot ->
            match slot.Contract |> Result.toOption |> Option.bind projection.Contracts.TryFind with
            | Some contract -> preturn contract
            | None -> fail (Message "Callable aggregate slot has no published receiving convention.")
        | None -> fail (Message "Callable aggregate has no published slot.")
    let expected = [0 .. contract.ParameterTypes.Length - 1] |> List.filter (fun ordinal -> not (List.contains ordinal contract.OmittedParameters))
    do! ensure (List.map fst contract.ParameterRepresentations = expected)
            "Callable aggregate receiving contract has no exact physical parameter inventory."
    let arguments = contract.ParameterRepresentations |> List.map (snd >> representationType)
    do! ensure (arguments |> List.forall ((<>) TVoid))
            "Callable aggregate receiving convention omitted no parameter at a physical unit slot."
    let result = representationType contract.ResultRepresentation
    return TFunc(arguments, if result = TVoid then [] else [result])
}

let private pStorage (row: CallableAggregateValue) (value: Val) = parser {
    let! state = getUserState
    let! slot =
        match state.Graph.Emission.Callable.AggregateSlots.TryFind row.Slot with
        | Some slot when state.Graph.Emission.Numeric.SourceTypes.TryFind row.Aggregate = Some slot.AggregateType -> preturn slot
        | _ -> fail (Message "Callable component storage has no exact enclosing type identity.")
    let! representation =
        match state.Graph.Emission.Numeric.OccurrenceRepresentations.TryFind row.Aggregate with
        | Some(Result.Ok representation) -> preturn representation
        | _ -> fail (Message "Callable component storage has no published aggregate representation.")
    let parent = { value with Type = physicalStorageType state.Platform.TargetArch value.Type }
    do! ensure (parent.Type = (representationType representation |> physicalStorageType state.Platform.TargetArch))
            "Callable component storage differs from its published enclosing data representation."
    // The authored ordinal route and each published parent placement determine
    // the views. This fold walks no source nodes and computes no byte layout.
    let! operations, storage, leaf =
        (preturn ([], parent, representation), slot.Path |> List.indexed)
        ||> List.fold (fun prior (depth, step) -> parser {
            let! operations, parent, representation = prior
            let! offset, child =
                match step, representation with
                | CallableAggregatePathStep.RecordField ordinal, ValueRepresentation.Record(fields, Some(offsets, _, _)) ->
                    match List.tryItem ordinal fields, List.tryItem ordinal offsets with
                    | Some(_, child), Some offset -> preturn (offset, child)
                    | _ -> fail (Message "Callable record component has no published declaration-ordinal placement.")
                | CallableAggregatePathStep.UnionPayload(caseOrdinal, 0), ValueRepresentation.Union(cases, Some(offset, _, _)) ->
                    match List.tryItem caseOrdinal cases with
                    | Some(_, [child]) -> preturn (offset, child)
                    | _ -> fail (Message "Callable union component requires its exact single-payload placement.")
                | _ -> fail (Message "Callable component route lacks a published record/union data layout.")
            let name = Values.aggregateComponent row.Occurrence row.Slot depth
            match child with
            | ValueRepresentation.CallableComponent(identity, ValueRepresentation.Record(_, Some(_, bytes, alignment)))
                when identity = row.Slot && depth = slot.Path.Length - 1 && bytes = row.Bytes && alignment = row.Alignment ->
                if bytes = 0 then return operations, parent, child
                else
                    let result = { SSA = name 60; Type = TMemRefStatic(bytes, TInt(IntWidth 8)) }
                    let! literal = pConstI (name 61) (int64 offset) TIndex
                    let! view = pMemRefView result.SSA parent.SSA (name 61) parent.Type result.Type
                    return operations @ [literal; view], result, child
            | ValueRepresentation.Record _ | ValueRepresentation.Union _ ->
                let childType = representationType child |> physicalStorageType state.Platform.TargetArch
                let result = { SSA = name 50; Type = childType }
                let! loads = pTypedExtractView result.SSA parent.SSA offset (name 51) (name 52) (name 53) childType parent.Type
                return operations @ loads, result, child
            | _ -> return! fail (Message "Callable component route does not end at its exact component data representation.")
        })
    do! ensure (row.Bytes >= 0 && row.Alignment > 0 &&
                (match leaf with ValueRepresentation.CallableComponent(identity, _) -> identity = row.Slot | _ -> false))
            "Callable aggregate component differs from its source-published placement."
    return operations, storage
}

let private pWrite (ctx: WitnessContext) (destination: Val) (row: CallableAggregateValue) = parser {
    do! ensure (row.Operation = CallableAggregateOperation.Construct || row.Operation = CallableAggregateOperation.Assign)
            "Callable aggregate write lacks a settled construction or assignment event."
    if row.Alternatives.IsEmpty then
        let! state = getUserState
        let absent =
            match state.Graph.Emission.Callable.AggregateSlots.TryFind row.Slot, row.Tag with
            | Some { Path = CallableAggregatePathStep.UnionPayload(caseOrdinal, _) :: _ }, Some tag -> tag.CaseOrdinal <> caseOrdinal
            | _ -> false
        do! ensure (row.Selector.IsNone && row.Value.IsNone && row.SelectedAlternative.IsNone &&
                    absent)
                "An absent union payload must have neither a callable value nor a selector."
        return []
    else
        let! state = getUserState
        let! alternative, actual =
            match row.SelectedAlternative, row.Value with
            | Some selected, Some value ->
                match row.Alternatives |> List.filter (fun alternative -> alternative.Ordinal = selected) with
                | [alternative] -> preturn (alternative, value)
                | _ -> fail (Message "Callable aggregate write has no unique selected source alternative.")
            | _ -> fail (Message "Callable aggregate write lacks its exact source value and selected alternative.")
        let! carrier = pAlternative row alternative
        let! value =
            match MLIRAccumulator.recallCallable actual state.Accumulator with
            | Some value when Operands.exactCarrier value = Some carrier -> preturn value
            | _ -> fail (Message "Callable aggregate write did not witness its exact paired source value.")
        let! shape =
            match Operands.project ctx actual with
            | Result.Ok shape -> preturn shape
            | Result.Error reason -> fail (Message reason)
        let! receivingType = pReceivingType row
        do! ensure ((Operands.code value).Type = Operands.functionType shape && receivingType = Operands.functionType shape)
                "Callable aggregate write has a changed function convention."
        let! storageOps, destination = pStorage row destination
        let name = Values.aggregateComponent row.Occurrence row.Slot alternative.Ordinal
        let! environmentOps =
            match alternative.EnvironmentPlacement, Operands.environment value with
            | None, None -> preturn []
            | Some placement, Some environment when environment.Type = TMemRefStatic(placement.ViewBytes, TInt(IntWidth 8)) ->
                pTypedInsertView destination.SSA environment.SSA placement.ByteOffset (name 0) (name 1) (name 2)
                                 environment.Type destination.Type
            | _ -> fail (Message "Callable aggregate write lost its actual environment operand.")
        let! selector = pSelector row
        let! selectorOps =
            match selector with
            | None -> preturn []
            | Some(offset, ty) -> parser {
                let! constant = pConstI (name 3) (int64 alternative.Ordinal) ty
                let! stores = pTypedInsertView destination.SSA (name 3) offset (name 4) (name 5) (name 6) ty destination.Type
                return constant :: stores
              }
        return storageOps @ environmentOps @ selectorOps
}

/// Compose writes into the aggregate data value already allocated by its owner.
let pWriteComponents (ctx: WitnessContext) occurrence aggregate destination = parser {
    let! rows = pRows occurrence
    do! ensure (rows |> List.forall (fun row -> row.Aggregate = aggregate))
            "Callable aggregate write names another destination occurrence."
    let! writes = rows |> List.map (pWrite ctx destination) |> Alex.XParsec.Extensions.sequence
    return List.concat writes
}

let pWithConstruction (ctx: WitnessContext) occurrence
                      (construction: PSGParser<MLIROp list * TransferResult>) = parser {
    let! operations, result = construction
    match result with
    | TRValue destination ->
        let! writes = pWriteComponents ctx occurrence occurrence destination
        return operations @ writes, result
    | _ -> return! fail (Message "Callable aggregate construction has no witnessed data storage.")
}

let pAssignComponents (ctx: WitnessContext) occurrence aggregate = parser {
    let! source, sourceType = pRecallNode aggregate
    let! writes = pWriteComponents ctx occurrence aggregate { SSA = source; Type = sourceType }
    return writes, TRVoid
}

/// A fold over published alternatives spells conditional regions. It does not
/// traverse source code or derive a dispatch family. The final arm is admitted
/// by the exact closed selector domain, not a fallback for an unknown value.
let private pSelect (row: CallableAggregateValue) lane (selector: Val option)
                    (arms: (int * MLIROp list * Val) list) = parser {
    match arms, selector with
    | [(_, operations, value)], None -> return operations, value
    | _ :: _, Some selector ->
        let _, finalOps, finalValue = List.last arms
        let! operations, result =
            (arms |> List.take (arms.Length - 1), preturn (finalOps, finalValue))
            ||> List.foldBack (fun (ordinal, operations, value) rest -> parser {
                let! fallbackOps, fallbackValue = rest
                do! ensure (value.Type = fallbackValue.Type)
                        "Callable aggregate alternatives lack a source-settled common physical convention."
                let name = Values.aggregateComponent row.Occurrence row.Slot ordinal
                let constant, condition = name lane, name (lane + 1)
                let result = { SSA = name (lane + 2); Type = value.Type }
                let! literal = pConstI constant (int64 ordinal) selector.Type
                let! compare = pCmpI condition ICmpPred.Eq selector.SSA constant selector.Type
                let! selectedYield = pSCFYield [value.SSA, value.Type]
                let! fallbackYield = pSCFYield [fallbackValue.SSA, fallbackValue.Type]
                let! conditional = pSCFIf condition (operations @ [selectedYield])
                                            (Some(fallbackOps @ [fallbackYield])) (Some(result.SSA, result.Type))
                return [literal; compare; conditional], result
            })
        return operations, result
    | _ -> return! fail (Message "Callable aggregate selection has no complete arm/selector correspondence.")
}

let pReadComponent (ctx: WitnessContext) occurrence aggregate = parser {
    let! state = getUserState
    let! rows = pRows occurrence
    let! row =
        match rows with
        | [row] when row.Aggregate = aggregate &&
                     (row.Operation = CallableAggregateOperation.Project || row.Operation = CallableAggregateOperation.Snapshot) -> preturn row
        | _ -> fail (Message "Callable aggregate read has no unique published slot and snapshot frontier.")
    let! raw, rawType = pRecallNode aggregate
    let! storageOps, storage = pStorage row { SSA = raw; Type = rawType }
    let! shape =
        match Operands.project ctx occurrence with
        | Result.Ok shape -> preturn shape
        | Result.Error reason -> fail (Message reason)
    let! receivingType = pReceivingType row
    do! ensure (receivingType = Operands.functionType shape)
            "Callable aggregate read differs from its exact receiving convention."
    let! selector = pSelector row
    let! selectorOps, selectorValue =
        match selector with
        | None -> preturn ([], None)
        | Some(offset, ty) -> parser {
            let name = Values.aggregateComponent occurrence row.Slot 0
            let value = { SSA = name 10; Type = ty }
            let! loads = pTypedExtractView value.SSA storage.SSA offset (name 11) (name 12) (name 13) ty storage.Type
            return loads, Some value
          }
    let! arms =
        row.Alternatives |> List.map (fun alternative -> parser {
            let! carrier = pAlternative row alternative
            let! implementation =
                match state.Graph.Nodes.TryFind carrier.Implementation with
                | Some implementation -> preturn implementation
                | None -> fail (Message "Callable aggregate alternative has no published implementation declaration.")
            let! alternativeShape =
                match Operands.project ctx alternative.Carrier with
                | Result.Ok shape -> preturn shape
                | Result.Error reason -> fail (Message reason)
            do! ensure (Operands.functionType shape = Operands.functionType alternativeShape &&
                        Operands.environmentType shape = Operands.environmentType alternativeShape)
                    "Callable aggregate selection has no source-settled common code and environment convention."
            let name = Values.aggregateComponent occurrence row.Slot alternative.Ordinal
            let code = { SSA = name 14; Type = Operands.functionType shape }
            let symbol = Alex.CodeGeneration.CallableSymbols.lambda state.Graph implementation false
            let! constant = pFuncConstant code.SSA symbol code.Type
            let! environment =
                match alternative.EnvironmentPlacement, Operands.environmentType shape with
                | None, None -> preturn None
                | Some placement, Some ty when ty = TMemRefStatic(placement.ViewBytes, TInt(IntWidth 8)) -> parser {
                    let value = { SSA = name 15; Type = ty }
                    let! loads = pTypedExtractView value.SSA storage.SSA placement.ByteOffset (name 16) (name 17) (name 18) ty storage.Type
                    return Some(loads, value)
                  }
                | _ -> fail (Message "Callable aggregate read lost its paired environment view.")
            return alternative.Ordinal, [constant], code, environment
        }) |> Alex.XParsec.Extensions.sequence
    let! codeOps, code = pSelect row 20 selectorValue (arms |> List.map (fun (ordinal, ops, code, _) -> ordinal, ops, code))
    let! environmentOps, environment =
        match Operands.environmentType shape with
        | None -> preturn ([], None)
        | Some _ -> parser {
            let! environments =
                arms |> List.map (fun (ordinal, _, _, environment) ->
                    match environment with
                    | Some(ops, value) -> preturn (ordinal, ops, value)
                    | None -> fail (Message "Callable aggregate selection dropped a required environment arm."))
                |> Alex.XParsec.Extensions.sequence
            let! ops, value = pSelect row 30 selectorValue environments
            return ops, Some value
          }
    let! result =
        match Operands.create shape code environment with
        | Result.Ok result -> preturn result
        | Result.Error reason -> fail (Message reason)
    return storageOps @ selectorOps @ codeOps @ environmentOps, TRCallable result
}
