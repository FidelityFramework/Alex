namespace Alex.XParsec

module PSGCombinators =
  type Parser<'a> = Parser of 'a
  type Builder() =
    member _.Bind(Parser value, next) = next value
    member _.Return value = Parser value
    member _.Delay f = f ()
  let parser = Builder()
  let ensure condition message = if condition then Parser () else failwith message
  let fail message : Result<'a, string> = Error message
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
