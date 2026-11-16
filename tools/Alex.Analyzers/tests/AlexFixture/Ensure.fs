namespace Alex.Dialects.Core

module Types =
  type SSA =
    | V of node: int * ordinal: int
    | Arg of int
    | CallableAlternative of node: int * alternative: int
    | AggregateComponent of node: int * slot: int * alternative: int * lane: int
    | ArrayElementIndex of node: int * element: int

namespace Alex.Traversal

module Values =
  open Alex.Dialects.Core.Types
  let value (Fidelity.PSG.NodeId node) (k: int) : SSA = V (node, k)
  let values (nodeId: Fidelity.PSG.NodeId) : SSA list = [ value nodeId 0; value nodeId 1 ]
  let meetValue (consumer: Fidelity.PSG.NodeId) (i: int) : SSA = value consumer (1000 + i)
  let returnMeetValue (lambdaId: Fidelity.PSG.NodeId) : SSA = value lambdaId 1100
  let unitReturnValue (lambdaId: Fidelity.PSG.NodeId) : SSA = value lambdaId 1101
  let callableCode (nodeId: Fidelity.PSG.NodeId) : SSA = value nodeId 1200
  let callableAlternative (Fidelity.PSG.NodeId node) (alternative: int) : SSA = CallableAlternative (node, alternative)
  let aggregateComponent (Fidelity.PSG.NodeId node) (Fidelity.PSG.NodeId slot) (alternative: int) (lane: int) : SSA = AggregateComponent (node, slot, alternative, lane)
  let arrayElementIndex (Fidelity.PSG.NodeId node) (element: int) : SSA = ArrayElementIndex (node, element)
  let prologueValue (lambdaId: Fidelity.PSG.NodeId) (k: int) : SSA = value lambdaId (2000 + k)
  let continuationValue (nodeId: Fidelity.PSG.NodeId) (slot: int) (lane: int) : SSA = value nodeId (4000 + 16 * slot + lane)
  let hardwareValue (bindingId: Fidelity.PSG.NodeId) (k: int) : SSA = value bindingId (3000 + k)
  let solverValue (k: int) : SSA = V (0, k)
  let undefined : SSA = V (-1, -1)
  let valuesOf (nodeId: Fidelity.PSG.NodeId) : Result<SSA list, string> = Result.Ok (values nodeId)
  let resultOf (nodeId: Fidelity.PSG.NodeId) : Result<SSA, string> = Result.Ok (value nodeId 0)

namespace Alex.XParsec

module PSGCombinators =
  let ensure (condition: bool) (message: string) = if condition then () else failwith message
  let fail (message: string) : Result<'a, string> = Error message
  type PSGParserState = { Graph: Fidelity.PSG.Revision; Current: Fidelity.PSG.SemanticNode; Zipper: int }
  let getNodeSSA (nodeId: Fidelity.PSG.NodeId) : Result<Alex.Dialects.Core.Types.SSA, string> = Alex.Traversal.Values.resultOf nodeId
  let getNodeSSAs (nodeId: Fidelity.PSG.NodeId) : Result<Alex.Dialects.Core.Types.SSA list, string> = Alex.Traversal.Values.valuesOf nodeId

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
