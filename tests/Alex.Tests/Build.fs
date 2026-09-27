/// Revisions assembled from contract values.
///
/// A test of a Pattern states the facts the Pattern is given and nothing else. No
/// compiler produces these revisions. They are contract values, and any value of the
/// contract is an input Alex must either witness or refuse with a reason.
module Alex.Tests.Build

open Fidelity.PSG
open Alex.Traversal.TransferTypes
open Alex.XParsec.PSGCombinators
module Zipper = Alex.Traversal.PSGZipper

let require label = Option.defaultWith (fun () -> failwith label)

let range : SourceRange =
    { File = "alex-test.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 0 } }

// The identities below are the frozen forms the compiler service publishes for its
// own built-in types. They were printed from the compiler service and copied here.
// A test that needs another type states it as a contract value in the same way.

let private constructor name kind : ConstructorIdentity =
    { Declaration = { Module = []; Name = name }; Parameters = []; NativeKind = Some kind }

let private unary name kind : ConstructorIdentity =
    { Declaration = { Module = []; Name = name }; Parameters = [ TypeParamKind.Type ]; NativeKind = kind }

let private dimensionless : Dimension = { Bases = Map.empty; Vars = Map.empty }

let private numeric name kind =
    TypeIdentity.Numeric(CarrierIdentity.Constructor(constructor name kind), dimensionless)

let unitType = TypeIdentity.Application(constructor "unit" NTUKind.NTUunit, [])
let boolType = TypeIdentity.Application(constructor "bool" NTUKind.NTUbool, [])
let charType = TypeIdentity.Application(constructor "char" NTUKind.NTUchar, [])
let stringType = TypeIdentity.Application(constructor "string" NTUKind.NTUstring, [])
let intType = numeric "int" (NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register))
let nintType = numeric "nativeint" (NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Pointer))
let uint8Type = numeric "uint8" (NTUKind.NTUuint(NTUWidth.Fixed 8))
let floatType = numeric "float" (NTUKind.NTUfloat(NTUWidth.Fixed 64))

let arrayOf element = TypeIdentity.Application(unary "array" (Some NTUKind.NTUarray), [ element ])
let optionOf element = TypeIdentity.Application(unary "option" None, [ element ])
let sequenceOf element = TypeIdentity.Sequence element
let enumeratorOf element = TypeIdentity.Enumerator element
let pointerTo element = TypeIdentity.NativePointer element
let functionFrom domain range = TypeIdentity.Function(domain, range)

/// One reachable node with the type, the children and the parent given.
let node (number: int) (kind: SemanticKind) (ty: TypeIdentity) (children: int list) (parent: int option) : SemanticNode =
    { Id = NodeId number
      Kind = kind
      Range = range
      Type = ty
      Children = List.map NodeId children
      Parent = Option.map NodeId parent
      IsReachable = true
      EmissionStrategy = EmissionStrategy.Inline
      ValueRange = None
      ObligationAnchors = [] }

/// A revision that holds the nodes given and states no other fact.
let revision (nodes: SemanticNode list) : Revision =
    { Revision.empty "alex-test" with Nodes = nodes |> List.map (fun held -> held.Id, held) |> Map.ofList }

/// The zipper at a node, reached from a root by the children named.
let at (revision: Revision) (root: int) (path: int list) : Zipper.PSGZipper =
    let step (position: Zipper.PSGZipper) (child: int) =
        let index = position.Focus.Children |> List.findIndex ((=) (NodeId child))
        Zipper.down index position |> require (sprintf "Node %d is not a child at this position" child)
    path |> List.fold step (Zipper.create revision (NodeId root) |> require (sprintf "Node %d is not held" root))

/// The zipper moved from a position to the child named.
let atChild (child: NodeId) (position: Zipper.PSGZipper) : Zipper.PSGZipper =
    let index = position.Focus.Children |> List.findIndex ((=) child)
    Zipper.down index position |> require "Fixture child is missing"

/// The zipper at a node the revision holds.
let focus (revision: Revision) (held: SemanticNode) : Zipper.PSGZipper =
    Zipper.create revision held.Id |> require (sprintf "Node %d is not held" (NodeId.value held.Id))

/// What a host selects for one witnessing: both widths declared, and the CPU forms.
let coeffects (pointerBits: int) : TransferCoeffects =
    { Platform =
        { TargetArch = { Register = Ok pointerBits; Pointer = Ok pointerBits }
          LinkedLibraries = Set.empty }
      TargetPlatform = Alex.Target.CPU }

/// Run a Pattern at a position.
let matchAt parser (position: Zipper.PSGZipper) pointerBits operands =
    tryMatchWithDiagnostics parser position.Graph position.Focus position (coeffects pointerBits) operands
