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
  // This file is outside XParsec/PSGCombinators.fs, so AXA009 refuses a Values.resultOf / Values.valuesOf call here.
  // The stubs supply the symbols and derive no name.
  let getNodeSSA (_: Fidelity.PSG.NodeId) : Result<Alex.Dialects.Core.Types.SSA, string> = Result.Error "stub"
  let getNodeSSAs (_: Fidelity.PSG.NodeId) : Result<Alex.Dialects.Core.Types.SSA list, string> = Result.Error "stub"

namespace Alex.Traversal

module PSGZipper =
  let focus (state: Alex.XParsec.PSGCombinators.PSGParserState) = state.Current

module SMTTransfer =
  let operations (obligations: string list) : Result<string list, string> = Result.Ok obligations
  let transfer (obligations: string list) : Result<string, string> = Result.Ok (String.concat "\n" obligations)

module ScopeContext =
  type ScopeLevel = ModuleLevel | FunctionLevel | BlockLevel
  type ScopeContext = { Id: int64; Level: ScopeLevel; Operations: string list; Parent: ScopeContext option }
  module ScopeContext =
    let root () : ScopeContext = { Id = 1L; Level = ModuleLevel; Operations = []; Parent = None }
    let createChild (parent: ScopeContext) (level: ScopeLevel) : ScopeContext = { Id = parent.Id + 1L; Level = level; Operations = []; Parent = Some parent }
    let addOp (op: string) (scope: ScopeContext) : ScopeContext = { scope with Operations = op :: scope.Operations }
    let addOps (ops: string list) (scope: ScopeContext) : ScopeContext = { scope with Operations = List.rev ops @ scope.Operations }
  let enterScope (depth: int) : int = depth + 1
  let exitScope (depth: int) : int = depth - 1

module TransferTypes =
  type MLIRAccumulator() =
    member val SSATypes: Map<string, string> = Map.empty with get, set
  module MLIRAccumulator =
    let recallNode (_: Fidelity.PSG.NodeId) (_: MLIRAccumulator) : (string * int) option = None
    let addError (_: string) (_: MLIRAccumulator) = ()
    let bindNode (_: Fidelity.PSG.NodeId) (_: Alex.Dialects.Core.Types.SSA) (_: string) (_: MLIRAccumulator) = ()
    let forgetVoid (_: Fidelity.PSG.NodeId) (_: MLIRAccumulator) = ()
    let completeVoid (_: Fidelity.PSG.NodeId) (_: int) (_: MLIRAccumulator) = ()
    let restoreOperands (_: Map<string, string>) (_: MLIRAccumulator) = ()
    let registerSSAType (_: Alex.Dialects.Core.Types.SSA) (_: string) (_: MLIRAccumulator) = ()

  type Diagnostic = { Message: string }
  module Diagnostic =
    let error (message: string) = { Message = message }

  type WitnessOutput = Ok | Error of Diagnostic | Skip
  module WitnessOutput =
    let error (message: string) = Error { Message = message }
    let errorCoded (_: int) (message: string) = Error { Message = message }
    let errorDiag (diag: Diagnostic) = Error diag
    let skip = Skip

module NanopassArchitecture =
  let visitAllNodes (witness: Fidelity.PSG.SemanticNode -> unit) (node: Fidelity.PSG.SemanticNode) : unit = witness node

namespace Alex.CodeGeneration

module TypeMapping =
  let mapInt () = 64

module CallableSymbols =
  let symbolFor (_: Fidelity.PSG.NodeId) = "sym"
