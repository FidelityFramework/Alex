namespace Fidelity.PSG

type Revision = { Header: int }
type SemanticNode = { Kind: int }
type OccurrenceBreadcrumb = { Ordinal: int }
type NominalTypeIdentity = { Module: string; Name: string }
type ConstructorIdentity = { Declaration: NominalTypeIdentity }
type TypeIdentity = Application of ConstructorIdentity * TypeIdentity list
type CaptureInfo = { Name: string }
