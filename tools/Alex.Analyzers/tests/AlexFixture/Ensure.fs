namespace Alex.XParsec

module PSGCombinators =
  let ensure (condition: bool) (message: string) = if condition then () else failwith message
  let fail (message: string) : Result<'a, string> = Error message
  type PSGParserState = { Graph: Fidelity.PSG.Revision; Current: Fidelity.PSG.SemanticNode; Zipper: int }

namespace Alex.Traversal

module PSGZipper =
  let focus (state: Alex.XParsec.PSGCombinators.PSGParserState) = state.Current

module TransferTypes =
  type MLIRAccumulator = { SSATypes: Map<string, string> }
  module MLIRAccumulator =
    let recallNode (_: Fidelity.PSG.NodeId) (_: MLIRAccumulator) : (string * int) option = None
    let addError (_: string) (_: MLIRAccumulator) = ()

  type Diagnostic = { Message: string }
  module Diagnostic =
    let error (message: string) = { Message = message }

  type WitnessOutput = Ok | Error of Diagnostic | Skip
  module WitnessOutput =
    let error (message: string) = Error { Message = message }
    let errorCoded (_: int) (message: string) = Error { Message = message }
    let errorDiag (diag: Diagnostic) = Error diag
    let skip = Skip

namespace Alex.CodeGeneration

module TypeMapping =
  let mapInt () = 64

module CallableSymbols =
  let symbolFor (_: Fidelity.PSG.NodeId) = "sym"
