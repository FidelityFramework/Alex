module Alex.InProject.DialectsCases

open Fidelity.PSG

let badNodesAccess (graph: Revision) (id: NodeId) = graph.Nodes.TryFind id

let rec badSemanticCata (kind: SemanticKind) =
  match kind with
  | SemanticKind.Literal value -> value
  | SemanticKind.Binding _ -> badSemanticCata kind

let badMutableLocal () =
  let mutable count = 0
  count <- 1
  count

let badRefCell () =
  let cell = ref 0
  cell.Value

let badDeclFactsRead (imp: BoundaryImport) =
  imp.DeclarationFacts.TryFind "x"

let cleanDeclFactsPresence (imp: BoundaryImport) =
  imp.DeclarationFacts.ContainsKey "x" && Map.containsKey "y" imp.DeclarationFacts

let badFallbackDefault (graph: Revision) (id: NodeId) =
  graph.Codata.Escapes.TryFind id |> Option.defaultValue 0

let cleanDomainOptional (alignmentOpt: string option) =
  alignmentOpt |> Option.defaultValue ""

let cleanRefusal (graph: Revision) (id: NodeId) =
  match graph.Codata.Escapes.TryFind id with
  | Some value -> Ok value
  | None -> Error "missing"
