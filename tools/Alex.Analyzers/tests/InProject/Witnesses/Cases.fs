module Alex.InProject.WitnessesCases

open Fidelity.PSG
open Alex.Traversal.TransferTypes

let badMutableLocal () =
  let mutable count = 0
  count <- 1
  count

let badRefCell () =
  let cell = ref 0
  cell.Value

let badBindNode (id: NodeId) (ssa: Alex.Dialects.Core.Types.SSA) (acc: MLIRAccumulator) =
  MLIRAccumulator.bindNode id ssa "i64" acc

let badVisitAll (node: SemanticNode) =
  Alex.Traversal.NanopassArchitecture.visitAllNodes ignore node

let cleanFold (values: int list) = values |> List.fold (fun total value -> total + value) 0

let cleanNodeSsa (id: NodeId) = Alex.XParsec.PSGCombinators.getNodeSSA id

let badSmtTransfer (obligations: string list) =
  Alex.Traversal.SMTTransfer.operations obligations
