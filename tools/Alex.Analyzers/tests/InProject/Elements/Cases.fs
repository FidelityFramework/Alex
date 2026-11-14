module Alex.InProject.ElementsCases

open Fidelity.PSG
open Alex.XParsec.PSGCombinators

let badNodeType (node: SemanticNode) = node.Kind
let badZipperCall (state: PSGParserState) = Alex.Traversal.PSGZipper.focus state
let badTypeMappingCall () = Alex.CodeGeneration.TypeMapping.mapInt ()
let badCallableSymbolsCall (id: NodeId) = Alex.CodeGeneration.CallableSymbols.symbolFor id
let badParserGraph (state: PSGParserState) = state.Graph.Header
let badParserZipper (state: PSGParserState) = state.Zipper
