module Alex.InProject.PatternsCases

open Fidelity.PSG
open Alex.Traversal.TransferTypes

let badBindNode (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) =
  MLIRAccumulator.bindNode id ssa "i64" acc

let badAccumulatorAssign (acc: MLIRAccumulator) =
  acc.SSATypes <- Map.empty

let badVisitAll (node: SemanticNode) =
  Alex.Traversal.NanopassArchitecture.visitAllNodes ignore node

let badScopeTransition (depth: int) =
  Alex.Traversal.ScopeContext.exitScope (Alex.Traversal.ScopeContext.enterScope depth)

let badSmtTransfer (obligations: string list) =
  Alex.Traversal.SMTTransfer.operations obligations, Alex.Traversal.SMTTransfer.transfer obligations

let cleanRecall (id: NodeId) (acc: MLIRAccumulator) =
  match MLIRAccumulator.recallNode id acc with
  | Some bound -> Result.Ok bound
  | None -> Result.Error "missing"

let cleanNodeSsa (id: NodeId) =
  Alex.XParsec.PSGCombinators.getNodeSSA id, Alex.XParsec.PSGCombinators.getNodeSSAs id

let badForgetVoid (id: NodeId) (acc: MLIRAccumulator) =
  MLIRAccumulator.forgetVoid id acc

let badScopeContext (ops: string list) =
  Alex.Traversal.ScopeContext.ScopeContext.addOps ops (Alex.Traversal.ScopeContext.ScopeContext.root ())
