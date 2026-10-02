module Alex.Tests.WitnessArtifactTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Traversal.ScopeContext
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

// The rows below are what the compiler service publishes for the fixture of this file.
// They were printed from the compiler service and copied here. The fixture holds
// three values of the bool type and no callable.

let private identities numbers = numbers |> List.map NodeId

/// One of the four domain nodes that settlement adds to the fixture. No code under
/// test reads them. They are held because the carriers name the first of them, and
/// because the node numbers of the revision are then the published ones.
let private domain number =
    { node number (SemanticKind.Literal NativeLiteral.Unit) unitType [] None with IsReachable = false }

let private element source target ordinal : Hyperedge =
    { Sources = [NodeId source]; Target = NodeId target
      Class = EdgeClass.Structural; Role = EdgeRole.Element; Ordinal = ordinal }

/// The carrier published for a value of the bool type.
let private boolean site participants : ScalarCarrier =
    { Site = NodeId site; Slot = SettledSlot.Bool; Range = ValueRange.Bounded(0I, 1I)
      Representation = None; Declaration = None; SourceType = boolType
      Obligations = []; Participants = Set.ofList (identities participants) }

let private carrierEdge (carrier: ScalarCarrier) : Hyperedge =
    { Sources = Set.toList carrier.Participants; Target = carrier.Site
      Class = EdgeClass.Range; Role = EdgeRole.NumericCarrier carrier; Ordinal = 0 }

/// The edges published among the nodes held: the relations the node kinds imply and
/// the carrier relations, in that order. The four domain edges and the provenance
/// edges of the domain nodes are left out. No code under test reads an edge.
let private withEdges implied carriers (revision: Revision) =
    { revision with Edges = implied @ List.map carrierEdge carriers }

/// Every held node is published as data that names itself.
let private withData units (revision: Revision) =
    let held = revision.Nodes |> Map.toList |> List.map fst
    { revision with
        Emission =
            { revision.Emission with
                Callable =
                    { revision.Emission.Callable with
                        ValueShapes = held |> List.map (fun id -> id, CallableValueShape.Data id) |> Map.ofList
                        AliasTargets = held |> List.map (fun id -> id, id) |> Map.ofList
                        UnitNodes = Set.ofList (identities units)
                        ClosedData = Set.ofList held
                        Supports = held |> List.map (fun id -> id, Set.singleton id) |> Map.ofList } } }

/// The numeric projection: a carrier for every value of the bool type, the sites whose
/// result the traversal checks, and the type and representation of every reachable node.
let private withNumeric (carriers: ScalarCarrier list) results (revision: Revision) =
    let sources = revision.Nodes |> Map.filter (fun _ held -> held.IsReachable)
    let form = Ok (ValueRepresentation.Scalar SettledSlot.Bool)
    { revision with
        Emission =
            { revision.Emission with
                Numeric =
                    { revision.Emission.Numeric with
                        Values = carriers |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList
                        Required = carriers |> List.map (fun carrier -> carrier.Site) |> Set.ofList
                        ResultSites = Set.ofList (identities results)
                        SourceTypes = sources |> Map.map (fun _ held -> held.Type)
                        OccurrenceRepresentations = sources |> Map.map (fun _ _ -> form)
                        TypeRepresentations = Map.ofList [boolType, form] } } }

let private fixture () =
    let first = node 0 (SemanticKind.Literal(NativeLiteral.Bool true)) boolType [] None
    let sibling = node 1 (SemanticKind.Literal(NativeLiteral.Bool false)) boolType [] None
    let root = node 2 (SemanticKind.Sequential [first.Id; sibling.Id]) boolType [0; 1] None
    let carriers = [boolean 0 [0; 3]; boolean 1 [1; 3]; boolean 2 [0; 1; 2; 3]]
    let graph =
        revision ([first; sibling; root] @ List.map domain [3; 4; 5; 6])
        |> withEdges [element 0 2 0; element 1 2 1] carriers
        |> withData [3; 4; 5; 6]
        |> withNumeric carriers [0; 1; 2]
        |> declareTraversalReadings
    let position = Zipper.create graph root.Id |> require "Missing fixture root" |> Zipper.down 0 |> require "Missing child"
    let accumulator = MLIRAccumulator.empty ()
    let rootScope = ref (ScopeContext.root ())
    let visited = ref Set.empty
    let context: WitnessContext =
        { Graph = graph; Zipper = position; Accumulator = accumulator; RootAccumulator = accumulator
          Coeffects = coeffects 64; ScopeContext = rootScope; RootScopeContext = rootScope
          GlobalVisited = visited; TraversalVisited = visited }
    context

[<Fact>]
let ``queued globals retain the draining witness occurrence`` () =
    let ctx = fixture ()
    let visited = ctx.GlobalVisited
    let globalOp = MLIROp.GlobalMemref("queued", TMemRefStatic(1, TInt(IntWidth 8)), None)
    // The occurrence is a result site of the bool type, so the witness returns a value
    // of the published carrier. The traversal refuses a result site that returns none.
    let witness (current: WitnessContext) (_: SemanticNode) =
        MLIRAccumulator.tryEmitGlobalMemref "queued" (TMemRefStatic(1, TInt(IntWidth 8))) None current.Accumulator
        { WitnessOutput.empty with Result = TRValue { SSA = Arg 0; Type = TInt(IntWidth 1) } }
    Alex.Traversal.NanopassArchitecture.visitAllNodes witness ctx ctx.Zipper.Focus visited
    Assert.Empty ctx.Accumulator.Errors
    let row = Assert.Single ctx.Accumulator.EmittedDefinitions
    Assert.Equal(globalOp, row.Operation)
    Assert.Same(ctx.Zipper.Focus, row.Occurrence.Focus)
    Assert.Equal(1, row.Occurrence.Path.Length)
    Assert.Empty ctx.Accumulator.PendingStaticGlobals

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``a refused result leaves no queued declaration for the next occurrence`` (refusedByWitness: bool) =
    let ctx = fixture ()
    let root = ctx.Zipper.Graph.Nodes[NodeId 2]
    let position = Zipper.create ctx.Zipper.Graph root.Id |> require "Missing fixture root"
    let ctx = { ctx with Zipper = position }
    // The first child queues a declaration and is refused: by its own witness, or by
    // the traversal because it returns no value at a result site. The second child
    // returns its value; the parent must refuse before running its own witness.
    let witness (current: WitnessContext) (held: SemanticNode) =
        if held.Id = NodeId 0 then
            MLIRAccumulator.tryEmitGlobalMemref "queued" (TMemRefStatic(1, TInt(IntWidth 8))) None current.Accumulator
            if refusedByWitness then WitnessOutput.error "The witness refuses this occurrence."
            else WitnessOutput.empty
        elif held.Id = root.Id then failwith "Parent witness ran after a required child was refused"
        else { WitnessOutput.empty with Result = TRValue { SSA = Arg (NodeId.value held.Id); Type = TInt(IntWidth 1) } }
    Alex.Traversal.NanopassArchitecture.visitAllNodes witness ctx ctx.Zipper.Focus ctx.GlobalVisited
    Assert.Equal(2, ctx.Accumulator.Errors.Length)
    let parentRefusal =
        ctx.Accumulator.Errors
        |> List.filter (fun diagnostic -> diagnostic.Phase = Some "required child occurrence")
        |> Assert.Single
    Assert.Equal(Some root.Id, parentRefusal.NodeId)
    Assert.Equal("The parent occurrence cannot be witnessed after a required child account or witness was refused.", parentRefusal.Message)
    let refusal =
        ctx.Accumulator.Errors
        |> List.filter (fun diagnostic -> diagnostic.Phase <> Some "required child occurrence")
        |> Assert.Single
    if refusedByWitness then Assert.Equal("The witness refuses this occurrence.", refusal.Message)
    else
        Assert.Equal(Some (NodeId 0), refusal.NodeId)
        Assert.Equal(Some "published numeric result", refusal.Phase)
        Assert.Equal("Witness result at node 0 omitted its source-published scalar value", refusal.Message)
    Assert.True((MLIRAccumulator.recallNode root.Id ctx.Accumulator).IsNone)
    // The declaration belonged to the refused occurrence. No later occurrence places it.
    Assert.Empty ctx.Accumulator.EmittedDefinitions
    Assert.Empty ctx.Accumulator.PendingStaticGlobals
    Assert.DoesNotContain(ScopeContext.getOps ctx.RootScopeContext.Value, fun operation ->
        match operation with MLIROp.GlobalMemref("queued", _, _) -> true | _ -> false)
