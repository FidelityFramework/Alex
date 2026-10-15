module Alex.Patterns.FunctionPointerPatterns

open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.XParsec.PSGCombinators
open XParsec
open XParsec.Parsers
open Alex.Elements.FuncElements

/// The receiving contract owns the native signature; the existing code-lifetime
/// publication owns the original closed implementation and symbol.
let closedFunctionAddress (graph: Revision) (site: NodeId) =
    let boundary = graph.Emission.Boundary
    match boundary.ClosedEntries.TryFind site with
    | Some entry when entry.Formation = site && entry.Lifetime.Implementation = entry.Implementation ->
        match graph.Emission.Callable.NativeEntries.TryFind entry.Implementation,
              boundary.CallbackInvocations.TryFind entry.Invocation,
              graph.Emission.Callable.Declarations.TryFind entry.Implementation with
        | Some symbol, Some invocation, Some declaration when invocation.Identity = entry.Invocation &&
                (declaration.Parameters |> List.map (fun (_, _, id) -> id)) = entry.Formals &&
                declaration.Result = entry.Body && declaration.Captures.IsEmpty &&
                entry.ParameterAdaptations.Length = entry.Formals.Length ->
            if invocation.Signature.Parameters.Length <> entry.Formals.Length then
                Result.Error "Closed native entry omitted an original native formal."
            else Result.Ok(entry, symbol, BoundaryAbi.signatureType invocation.Signature)
        | _ -> Result.Error "Closed native entry lacks its exact invocation signature and complete declaration."
    | _ -> Result.Error "A native function address lacks its original ProgramImage code lifetime and symbol."

let pClosedFunctionAddress (site: NodeId) (symbol: string) (implementation: NodeId) : PSGParser<MLIROp list * TransferResult> =
    parser {
        let! state = getUserState
        match closedFunctionAddress state.Graph site with
        | Result.Ok(entry, actualSymbol, ty) when entry.Implementation = implementation && actualSymbol = symbol ->
            let! ssa = getNodeSSA site
            let! operation = pFuncConstant ssa symbol ty
            return [operation], TRValue { SSA = ssa; Type = ty }
        | Result.Ok _ -> return! fail (Message "A native function address differs from its original closed implementation and symbol.")
        | Result.Error reason -> return! fail (Message reason)
    }

let pFunctionAddress (_site: NodeId) (_symbol: string) (_parameters: MLIRType list) (_result: MLIRType) : PSGParser<MLIROp list * TransferResult> =
    fail (Message "A native function address requires a source-published target ABI realization; function/index repair casts are retired")

let pFunctionPointerCall (_site: NodeId) (_pointer: SSA) (_arguments: Val list) (_result: MLIRType) : PSGParser<MLIROp list * TransferResult> =
    fail (Message "A native function-pointer call requires a source-published target ABI realization; function/index repair casts are retired")
