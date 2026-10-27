module Alex.Patterns.MmioPatterns
open XParsec
open XParsec.Parsers
open XParsec.Combinators
open Alex.XParsec.PSGCombinators
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Elements.MLIRAtomics
open Alex.CodeGeneration.TypeMapping
open Fidelity.PSG

let pMmioIntrinsic : PSGParser<MLIROp list * TransferResult> = parser {
    let! node = getCurrentNode
    let! state = getUserState
    let! declared =
        match Map.tryFind node.Id state.Graph.Foreign.Mmio with
        | Some declared -> preturn declared
        | None -> fail (Message (sprintf "MMIO occurrence %d has no published Foreign.Mmio descriptor" (NodeId.value node.Id)))
    let operation, args = declared.Operation, declared.Arguments
    let! ssas = getNodeSSAs node.Id
    let s i = ssas.[i]
    let isReg = operation.StartsWith("reg") || operation.StartsWith("bind")
    let isRead = operation.StartsWith("read")
    let! evidence =
        match Map.tryFind node.Id state.Graph.Codata.Mmio with
        | Some evidence -> preturn evidence
        | None -> fail (Message "MMIO operation has no established CCS access evidence")
    let bits = evidence.Bits
    do! ensure (bits = 8 || bits = 16 || bits = 32) "Unsupported MMIO access width"
    if isReg then
        let addressTy = pointerTypeAt state.Graph node.Id
        return [MLIROp.ArithOp (ArithOp.ConstI (s 0, evidence.Address, addressTy))], TRValue { SSA = s 0; Type = addressTy }
    else
        do! ensure (args.Length = (if isRead then 1 else 2)) "Invalid MMIO accessor arity"
        let publishedTy = pointerTypeAt state.Graph args.Head
        let! address, addressTy = pRecallNode args.Head
        do! ensure (addressTy = publishedTy) "MMIO handle differs from its published pointer representation"
        let elementTy = TInt (IntWidth bits)
        if isRead then
            return [MLIROp.MmioLoad (node.Id, s 0, address, bits)], TRValue { SSA = s 0; Type = elementTy }
        else
            // The stored value is adapted by the published meet of this occurrence and
            // its operand. No cast is selected from the physical widths.
            let! value, ty = pRecallNode args.[1]
            do! ensure (match ty with TInt _ -> true | _ -> false) "MMIO write requires an integer"
            let! conversion, stored = pSettledAdaptTo node.Id args.[1] elementTy { SSA = value; Type = ty }
            return! Alex.Patterns.LiteralPatterns.pWithUnitResult node.Id
                        (preturn (conversion @ [MLIROp.MmioStore (node.Id, stored.SSA, address, bits)], TRVoid))
}
