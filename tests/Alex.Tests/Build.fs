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

/// Declare the positional accounts of a known finite component fixture. All
/// paths through shared children are retained; Parent metadata is not a path.
/// This is fixture authoring, never a production navigation or authority step.
let declareTraversalReadings (graph: Revision) : Revision =
    let live = graph.Nodes |> Map.filter (fun _ body -> body.IsReachable)
    let structural =
        live |> Map.toList |> List.map (fun (id, body) ->
            let stamp = sprintf "fixture:structural:%d:%A" (NodeId.value id) body.Children
            let positions = body.Children |> List.indexed |> List.filter (fun (_, child) -> live.ContainsKey child) |> Map.ofList
            (id, OccurrencePort.StructuralChild), ({ Extent = body.Children.Length; Stamp = stamp; Positions = positions }: SourcePortAccount))
    let modules =
        graph.Nodes |> Map.toList |> List.choose (fun (id, body) ->
            match body.Kind with
            | SemanticKind.ModuleDef(name, members) ->
                let positions = members |> List.indexed |> List.filter (fun (_, child) -> live.ContainsKey child) |> Map.ofList
                let account : SourcePortAccount =
                    { Extent = members.Length; Stamp = sprintf "fixture:declarations:%d:%A" (NodeId.value id) members; Positions = positions }
                Some(id, name, account)
            | _ -> None)
    let ports =
        structural @ (modules |> List.map (fun (id, _, account) -> (id, OccurrencePort.ModuleDeclaration), account)) |> Map.ofList
    let parents =
        ports |> Map.toList |> List.collect (fun ((parent, port), account) ->
            account.Positions |> Map.toList |> List.map (fun (ordinal, child) ->
                child, ({ Parent = parent; Port = port; Ordinal = ordinal; Extent = account.Extent; Stamp = account.Stamp }: OccurrenceBreadcrumb)))
        |> List.groupBy fst |> List.map (fun (child, frames) -> child, List.map snd frames) |> Map.ofList
    let rec paths (seen: Set<NodeId>) (id: NodeId) =
        if seen |> Set.contains id then failwithf "Fixture positional declaration contains a structural cycle at %d" (NodeId.value id)
        else
            match parents.TryFind id with
            | None -> [[]]
            | Some frames -> frames |> List.collect (fun frame -> paths (seen.Add id) frame.Parent |> List.map (fun outer -> frame :: outer))
    let positions = Set.union (live.Keys |> Set.ofSeq) (modules |> List.map (fun (id, _, _) -> id) |> Set.ofList)
    let contexts = positions |> Seq.map (fun id -> id, paths Set.empty id) |> Map.ofSeq
    let children =
        live |> Map.map (fun _ body ->
            body.Children |> List.mapi (fun ordinal child ->
                { Ordinal = ordinal
                  Traversal =
                    if live.ContainsKey child then ChildTraversal.EnterLocal child
                    else ChildTraversal.SourceOmitted(SupportKey.WholeOwningAnalysisRegion "fixture-owner", child) }))
    let headers = modules |> List.map (fun (id, name, account) ->
        id, ({ Identity = id; Name = name; Ports = Map.ofList [OccurrencePort.ModuleDeclaration, account] }: SourceContextHeader)) |> Map.ofList
    let entries =
        contexts |> Map.toList |> List.choose (fun (id, paths) ->
            if live.ContainsKey id && List.contains [] paths then
                Some ({ Focus = id; Reason = SourceEntryReason.ExecutableRoot; Context = [] }: SourceWitnessEntry)
            else None)
    let claims = graph.Nodes.Values |> Seq.choose (fun node ->
        match node.Kind with SemanticKind.Obligation info -> Some(node.Id, info) | _ -> None) |> Map.ofSeq
    { graph with
        SourceReadings =
            { graph.SourceReadings with Entries = entries; Ports = ports; Children = children; Contexts = contexts; ContextHeaders = headers }
        CurrentClaims = claims }

/// Explicit component-fixture declaration of the rows Baker publishes for
/// these synthetic bindings. Production witnesses never perform this reading.
/// Call once after stating the fixture's projections; observation cannot repair
/// a missing or changed account, and `revision` itself still states no facts.
let declareBindingReadings (graph: Revision) : Revision =
    let callable = graph.Emission.Callable
    let storage = graph.Emission.Storage
    let uses = graph.Nodes |> Map.toList |> List.choose (fun (site, node) ->
        match node.Kind with
        | SemanticKind.VarRef(_, Some binding) ->
            let name, bindingClass =
                match graph.Nodes.TryFind binding with
                | Some { Kind = SemanticKind.PatternBinding name } -> name, SourceBindingClass.Formal
                | Some { Kind = SemanticKind.Binding(name, false, _, _) } -> name, SourceBindingClass.ImmutableValue
                | Some { Kind = SemanticKind.Binding(name, true, _, _) } -> name, SourceBindingClass.MutableCell
                | Some { Kind = SemanticKind.Lambda _ } -> sprintf "lambda_%d" (NodeId.value binding), SourceBindingClass.ImmutableValue
                | Some { Kind = SemanticKind.SeqExpr _ } -> sprintf "sequence_%d" (NodeId.value binding), SourceBindingClass.ImmutableValue
                | Some { Kind = SemanticKind.LazyExpr _ } -> sprintf "lazy_%d" (NodeId.value binding), SourceBindingClass.ImmutableValue
                | Some { Kind = SemanticKind.ClosureValue _ } -> sprintf "closure_%d" (NodeId.value binding), SourceBindingClass.ImmutableValue
                | Some body -> failwithf "Fixture binding-use declaration cannot state binding %d with kind %A" (NodeId.value binding) body.Kind
                | None -> failwithf "Fixture binding-use declaration requires known binding %d" (NodeId.value binding)
            Some(site,
                { Binding = binding; Name = name; Class = bindingClass
                  IsProgramSlotIntent = storage.Startup |> Option.exists (fun plan -> plan.ValueBindings.Contains binding)
                  HasProgramSlotAuthority = storage.SlotAuthorities.Contains binding
                  IsFunctionBinding = callable.FunctionBindings.Contains binding
                  IsCallableDeclaration = callable.DefinitionOnlyBindings.Contains binding || callable.DefinitionOnlyLambdas.Contains binding
                  IsPartialApplication = graph.Codata.Curry.PartialAppBindings.Contains binding })
        | _ -> None) |> Map.ofList
    { graph with SourceReadings = { graph.SourceReadings with BindingUses = uses } }
    |> declareTraversalReadings
