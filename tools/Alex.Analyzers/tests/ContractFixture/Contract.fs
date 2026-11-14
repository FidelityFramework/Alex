namespace Fidelity.PSG

type NodeId = NodeId of int
type SemanticKind = Literal of int | Binding of string
type SemanticNode = { Kind: SemanticKind }
type CodataMeets = { Escapes: Map<NodeId, int> }
type BoundaryImport = { DeclarationFacts: Map<string, string> }
type IntrinsicWriteImport = { Fd: int }
type SpatialModuleWitness = { Scope: NodeId }
type BoundaryScalar = ScalarInt of int
type EmissionProjection = { Entries: Map<NodeId, string> }
type Revision = { Header: int; Nodes: Map<NodeId, SemanticNode>; Codata: CodataMeets; Emission: EmissionProjection }
type OccurrenceBreadcrumb = { Ordinal: int }
type NominalTypeIdentity = { Module: string; Name: string }
type ConstructorIdentity = { Declaration: NominalTypeIdentity }
type TypeIdentity = Application of ConstructorIdentity * TypeIdentity list
type CaptureInfo = { Name: string }

module Revision =
  let tryNode (id: NodeId) (revision: Revision) = revision.Nodes.TryFind id
