module Alex.Patterns.MmioPatterns
open XParsec
open XParsec.Parsers
open XParsec.Combinators
open Alex.XParsec.PSGCombinators
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Elements.MLIRAtomics
open Fidelity.PSG

let pMmioIntrinsic : PSGParser<MLIROp list * TransferResult> = parser {
    let! info, args = pIntrinsicApplication IntrinsicModule.Mmio
    let! node = getCurrentNode
    let! state = getUserState
    let! ssas = getNodeSSAs node.Id
    let s i = ssas.[i]
    let isReg = info.Operation.StartsWith("reg") || info.Operation.StartsWith("bind")
    let isRead = info.Operation.StartsWith("read")
    let! evidence =
        match Map.tryFind node.Id state.Graph.Codata.Mmio with
        | Some evidence -> preturn evidence
        | None -> fail (Message "MMIO operation has no established CCS access evidence")
    let bits = evidence.Bits
    do! ensure (bits = 8 || bits = 16 || bits = 32) "Unsupported MMIO access width"
    if isReg then
        // ConstI carries signed bits; a high 64-bit CPU address is the same
        // pointer bit pattern after index-to-pointer conversion.
        let address = int64 (if evidence.Address > bigint System.Int64.MaxValue then evidence.Address - (1I <<< 64) else evidence.Address)
        return [MLIROp.ArithOp (ArithOp.ConstI (s 0, address, TIndex))], TRValue { SSA = s 0; Type = TIndex }
    else
        do! ensure (args.Length = (if isRead then 1 else 2)) "Invalid MMIO accessor arity"
        let handleType = state.Graph.Nodes.[args.Head].Type
        do! ensure (match handleType with TypeIdentity.Application(constructor, []) -> constructor.Declaration.Name = "Mmio" + string bits | _ -> false)
                   "MMIO access width does not match its opaque register handle"
        let! address, addressTy = pRecallNode args.Head
        do! ensure (addressTy = TIndex) "MMIO handle must have the platform pointer representation"
        let elementTy = TInt (IntWidth bits)
        if isRead then
            return [MLIROp.MmioLoad (s 0, address, s 1, s 2, bits)], TRValue { SSA = s 0; Type = elementTy }
        else
            // The stored value is adapted by the published meet of this occurrence and
            // its operand. No cast is selected from the physical widths.
            let! value, ty = pRecallNode args.[1]
            do! ensure (match ty with TInt _ -> true | _ -> false) "MMIO write requires an integer"
            let! conversion, stored = pSettledAdaptTo node.Id args.[1] elementTy { SSA = value; Type = ty }
            return! Alex.Patterns.LiteralPatterns.pWithUnitResult node.Id
                        (preturn (conversion @ [MLIROp.MmioStore (stored.SSA, address, s 1, s 2, bits)], TRVoid))
}
