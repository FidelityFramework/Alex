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
let pClosedFunctionAddress (site: NodeId) (symbol: string) (implementation: NodeId) : PSGParser<MLIROp list * TransferResult> =
    parser {
        let! state = getUserState
        let graph = state.Graph
        let boundary = graph.Emission.Boundary
        match boundary.ClosedEntries.TryFind site with
        | Some entry when entry.Formation = site && entry.Implementation = implementation &&
                          entry.Lifetime.Implementation = implementation &&
                          graph.Emission.Callable.NativeEntries.TryFind implementation = Some symbol ->
            match boundary.CallbackInvocations.TryFind entry.Invocation,
                  graph.Emission.Callable.Declarations.TryFind implementation with
            | Some invocation, Some declaration when invocation.Identity = entry.Invocation &&
                    (declaration.Parameters |> List.map (fun (_, _, id) -> id)) = entry.Formals &&
                    declaration.Result = entry.Body && declaration.Captures.IsEmpty &&
                    entry.ParameterAdaptations.Length = entry.Formals.Length ->
                let ty = BoundaryAbi.signatureType invocation.Signature
                do! ensure (invocation.Signature.Parameters.Length = entry.Formals.Length)
                        "Closed native entry omitted an original native formal."
                let! ssa = getNodeSSA site
                let! operation = pFuncConstant ssa symbol ty
                return [operation], TRValue { SSA = ssa; Type = ty }
            | _ -> return! fail (Message "Closed native entry lacks its exact invocation signature and complete declaration.")
        | _ -> return! fail (Message "A native function address lacks its original ProgramImage code lifetime and symbol.")
    }

let pFunctionAddress (_site: NodeId) (_symbol: string) (_parameters: MLIRType list) (_result: MLIRType) : PSGParser<MLIROp list * TransferResult> =
    fail (Message "A native function address requires a source-published target ABI realization; function/index repair casts are retired")

let pFunctionPointerCall (_site: NodeId) (_pointer: SSA) (_arguments: Val list) (_result: MLIRType) : PSGParser<MLIROp list * TransferResult> =
    fail (Message "A native function-pointer call requires a source-published target ABI realization; function/index repair casts are retired")
