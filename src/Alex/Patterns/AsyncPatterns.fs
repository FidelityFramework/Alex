/// Observe the async formation and activation rows the revision publishes
/// (Codata.AsyncFormations, Codata.AsyncActivations). A formation is the value
/// of its deferred callable under the formation's own published carrier and
/// emits no operation. An activation is one call of the activated callable.
/// Neither Pattern recognizes a builder, numbers a suspension, constructs a
/// frame or supplies an operand the revision does not name.
module Alex.Patterns.AsyncPatterns

open XParsec
open XParsec.Parsers
open XParsec.Combinators
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.XParsec.PSGCombinators
open Alex.Elements.FuncElements
module Operands = Alex.Traversal.CallableOperands

let private pWitnessedCallable (role: string) (owner: NodeId) (occurrence: NodeId) : PSGParser<CallableOperand * CallableCarrier> = parser {
    let! state = getUserState
    match MLIRAccumulator.recallCallable occurrence state.Accumulator with
    | None ->
        return! fail (Message (sprintf "%s %d: callable occurrence %d has no witnessed callable operands in this operation scope." role (NodeId.value owner) (NodeId.value occurrence)))
    | Some value ->
        match Operands.exactCarrier value with
        | Some carrier -> return value, carrier
        | None ->
            return! fail (Message (sprintf "%s %d: callable occurrence %d has no exact published carrier (Emission.Callable.Carriers)." role (NodeId.value owner) (NodeId.value occurrence)))
}

/// The formation row names the deferred callable. The formation occurrence and
/// its final child are published as two carriers of that one implementation,
/// related by a published transport. The code and environment operands of the
/// final child become the formation's operands. The body is not entered here
/// and no call is emitted.
let pAsyncFormation (ctx: WitnessContext) (row: AsyncFormation) : PSGParser<MLIROp list * TransferResult> = parser {
    let! state = getUserState
    do! ensure (state.Current.Id = ctx.Zipper.Focus.Id && state.Zipper = ctx.Zipper && state.Current.Id = row.Formation)
            "Async formation requires its current Huet occurrence."
    let formation = NodeId.value row.Formation
    let! source =
        match List.tryLast state.Current.Children with
        | Some source -> preturn source
        | None -> fail (Message (sprintf "Async formation %d has no deferred callable occurrence among its children." formation))
    let projection = state.Graph.Emission.Callable
    let! transports =
        match projection.Transports.TryFind row.Formation with
        | Some sources -> preturn sources
        | None -> fail (Message (sprintf "Async formation %d has no published callable transport row (Emission.Callable.Transports)." formation))
    do! ensure (transports.Contains source)
            (sprintf "Async formation %d: Emission.Callable.Transports does not name its deferred callable occurrence %d as a source." formation (NodeId.value source))
    let! deferred, deferredCarrier = pWitnessedCallable "Async formation" row.Formation source
    let! formed =
        match projection.Carriers.TryFind row.Formation with
        | Some carrier -> preturn carrier
        | None -> fail (Message (sprintf "Async formation %d has no published callable carrier (Emission.Callable.Carriers)." formation))
    do! ensure (deferredCarrier.Implementation = row.Callable && formed.Implementation = row.Callable)
            (sprintf "Async formation %d: its published deferred callable %d is not the implementation of the formation carrier and of occurrence %d." formation (NodeId.value row.Callable) (NodeId.value source))
    do! ensure (formed.Environment = deferredCarrier.Environment && formed.Contract = deferredCarrier.Contract && formed.Kind = deferredCarrier.Kind)
            (sprintf "Async formation %d and its deferred callable occurrence %d disagree on the published environment convention, contract or carrier kind." formation (NodeId.value source))
    let! shape = pFromResult (Operands.project ctx row.Formation)
    let! value = pFromResult (Operands.create shape (Operands.code deferred) (Operands.environment deferred))
    return [], TRCallable value
}

/// The activation row names the formation; the application's one operand
/// carries the activated callable. The call passes the operand's environment
/// and nothing else. A physical formal of the deferred callable with no
/// published argument occurrence at the site is refused: the Pattern supplies
/// no unit token, zero or default for it.
let pAsyncActivation (ctx: WitnessContext) (row: AsyncActivation) : PSGParser<MLIROp list * TransferResult> = parser {
    let! state = getUserState
    do! ensure (state.Current.Id = ctx.Zipper.Focus.Id && state.Zipper = ctx.Zipper && state.Current.Id = row.Site)
            "Async activation requires its current Huet occurrence."
    let site = NodeId.value row.Site
    let! formation =
        match state.Graph.Codata.AsyncFormations.TryFind row.Formation with
        | Some formation -> preturn formation
        | None -> fail (Message (sprintf "Async activation %d names formation %d, which has no Codata.AsyncFormations row." site (NodeId.value row.Formation)))
    let! _, arguments = pApplication
    let! operand =
        match arguments with
        | [operand] -> preturn operand
        | _ -> fail (Message (sprintf "Async activation %d is not an application to exactly one activated computation." site))
    let! activated, carrier = pWitnessedCallable "Async activation" row.Site operand
    do! ensure (carrier.Implementation = formation.Callable)
            (sprintf "Async activation %d: operand %d carries implementation %d, and the published formation %d names deferred callable %d." site (NodeId.value operand) (NodeId.value carrier.Implementation) (NodeId.value row.Formation) (NodeId.value formation.Callable))
    let! shape = pFromResult (Operands.project ctx operand)
    let groups = Operands.parameterTypes shape
    do! ensure (groups.Length = carrier.Parameters.Length)
            (sprintf "Async activation %d: the published parameters of deferred callable %d do not match its physical parameter components." site (NodeId.value carrier.Implementation))
    let formals = List.zip carrier.Parameters groups
    let! declared =
        match carrier.Environment, formals with
        | None, formals -> preturn formals
        | Some convention, ((_, _, formal), _) :: rest when formal = convention.Formal -> preturn rest
        | Some _, _ -> fail (Message (sprintf "Async activation %d: the environment of deferred callable %d is not its first published formal." site (NodeId.value carrier.Implementation)))
    do! ensure (carrier.Environment.IsSome = (Operands.environment activated).IsSome)
            (sprintf "Async activation %d: operand %d does not carry the environment its published convention requires." site (NodeId.value operand))
    match declared |> List.tryFind (fun (_, components) -> not components.IsEmpty) with
    | Some ((name, _, formal), _) ->
        return! fail (Message (sprintf "Async activation %d: Codata.AsyncActivations publishes no argument occurrence for formal %d (%s) of deferred callable %d, and Emission.Ordinary.Parameters does not publish that formal as omitted." site (NodeId.value formal) name (NodeId.value carrier.Implementation)))
    | None ->
        let! resultType =
            match Operands.resultTypes shape with
            | [single] -> preturn single
            | _ -> fail (Message (sprintf "Async activation %d: deferred callable %d does not publish exactly one physical result component." site (NodeId.value carrier.Implementation)))
        let! result = getNodeSSA row.Site
        let! call =
            pFuncCallIndirectResults [{ SSA = result; Type = resultType }] (Operands.code activated).SSA (Option.toList (Operands.environment activated))
        let! adaptations, value, valueType = pAdapt row.Site row.Site result resultType
        return call :: adaptations, TRValue { SSA = value; Type = valueType }
}
