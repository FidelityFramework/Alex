/// Project resolved PSG callable identity into an emission symbol.
/// Local source names are scoped; module and external names retain their ABI spelling.
module Alex.CodeGeneration.CallableSymbols

open Fidelity.PSG

let private render = function
    | CallableSymbolName.ModuleBinding(moduleName, name) -> moduleName + "." + name
    | CallableSymbolName.LocalBinding(id, name) -> sprintf "__clef_local_%d_%s" (NodeId.value id) name
    | CallableSymbolName.RootBinding name -> name
    | CallableSymbolName.Anonymous id -> sprintf "lambda_%d" (NodeId.value id)

/// The published symbol of a callable binding. None when the projection publishes none for it.
let tryBinding (graph: Revision) (id: NodeId) : string option =
    graph.Emission.Callable.Symbols.TryFind id |> Option.map render

let lambda (graph: Revision) (node: SemanticNode) _hasClosureLayout : string =
    match tryBinding graph node.Id with
    | Some symbol -> symbol
    | None ->
        invalidOp (sprintf "PSG settlement (WitnessEmission) did not settle a declaration symbol for the callable code at node %d" (NodeId.value node.Id))
