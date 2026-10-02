/// Witness an always-active source requirement. Baker supplies the condition,
/// diagnostic and ordered continuation; this pattern supplies no failure policy.
module Alex.Patterns.RequirementPatterns

open XParsec
open XParsec.Parsers
open XParsec.Combinators
open Alex.XParsec.PSGCombinators
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Elements.CFElements
open Alex.Patterns.LiteralPatterns

let pRequirement (ctx: WitnessContext) = parser {
    let! state = getUserState
    do! ensure (obj.ReferenceEquals(state.Zipper, ctx.Zipper)
                && obj.ReferenceEquals(ctx.Graph, ctx.Zipper.Graph)
                && state.Current.Id = ctx.Zipper.Focus.Id)
            "Requirement must be witnessed at its actual zipper occurrence."
    let! contract =
        match ctx.Graph.Emission.Storage.Requirements.TryFind state.Current.Id with
        | Some contract -> preturn contract
        | None -> fail (Message "Requirement has no source-published ordered contract.")
    do! ensure (match ctx.Zipper.Path with
                | step :: _ -> step.Parent = contract.Frontier
                               && step.Port = Fidelity.PSG.OccurrencePort.StructuralChild
                               && step.Ordinal = 0 && step.Extent = 2
                               && (ctx.Graph.SourceReadings.Ports.TryFind (step.Parent, step.Port)
                                   |> Option.exists (fun account ->
                                       account.Stamp = step.Stamp && account.Extent = step.Extent
                                       && account.Positions.TryFind 0 = Some contract.Site
                                       && account.Positions.TryFind 1 = Some contract.Continuation))
                | [] -> false)
            "Requirement is outside its admitted source frontier."
    let! condition, conditionType = pRecallNode contract.Condition
    do! ensure (conditionType = TInt(IntWidth 1)) "Requirement condition must retain its Boolean carrier."
    let! operation = pAssert condition contract.Diagnostic
    return! pWithUnitResult contract.Site (preturn ([operation], TRVoid))
}
