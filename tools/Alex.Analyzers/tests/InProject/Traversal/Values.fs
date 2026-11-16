namespace Alex.Dialects.Core

module Types =
  type SSA =
    | V of node: int * ordinal: int
    | Arg of int
    | CallableAlternative of node: int * alternative: int
    | AggregateComponent of node: int * slot: int * alternative: int * lane: int
    | ArrayElementIndex of node: int * element: int

namespace Alex.Traversal

// Acceptance case: this file is at Traversal/Values.fs, the one path where AXA009 admits
// SSA union case construction and direct use of every SSA-producing member of Values.
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
