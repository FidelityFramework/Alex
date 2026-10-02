module Alex.Tests.UnitResultTests

open Xunit
open XParsec
open XParsec.Parsers
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.XParsec.PSGCombinators
open Alex.Patterns.LiteralPatterns
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

let private identities = List.map NodeId >> Set.ofList

/// The target node of one settled domain relation. The compiler service adds one for each
/// of the numeric, memory, spatial and boundary domains. It is a unit literal that is not reachable.
let private domainNode number =
    { node number (SemanticKind.Literal NativeLiteral.Unit) Alex.Tests.Build.unitType [] None with IsReachable = false }

/// The callable rows published for the fixture. Every occurrence is data. The binding
/// names the values of the conditional it holds.
let private callable : CallableEmissionProjection =
    { Empty.callable with
        ValueShapes = [0 .. 8] |> List.map (fun site -> NodeId site, CallableValueShape.Data(NodeId site)) |> Map.ofList
        Symbols = Map.ofList [ (NodeId 4, CallableSymbolName.RootBinding "effectResult") ]
        AliasTargets =
            [0, 0; 1, 1; 2, 2; 3, 3; 4, 3; 5, 5; 6, 6; 7, 7; 8, 8]
            |> List.map (fun (site, target) -> NodeId site, NodeId target) |> Map.ofList
        UnitNodes = identities [1 .. 8]
        ClosedData = identities [0 .. 8]
        Supports =
            [0, [0]; 1, [1]; 2, [2]; 3, [3]; 4, [3; 4]; 5, [5]; 6, [6]; 7, [7]; 8, [8]]
            |> List.map (fun (site, support) -> NodeId site, identities support) |> Map.ofList }

/// The numeric rows published for the fixture. The guard is the one scalar carrier.
let private numeric : NumericWitnessProjection =
    let unitIdentity = Alex.Tests.Build.unitType
    { Empty.numeric with
        Values =
            Map.ofList
                [ (NodeId 0,
                   { Site = NodeId 0
                     Slot = SettledSlot.Bool
                     Range = ValueRange.Bounded(0I, 1I)
                     Representation = None
                     Declaration = None
                     SourceType = boolType
                     Obligations = []
                     Participants = identities [0; 5] }) ]
        Required = identities [0]
        SourceTypes =
            Map.ofList
                [ NodeId 0, boolType; NodeId 1, unitIdentity; NodeId 2, unitIdentity
                  NodeId 3, unitIdentity; NodeId 4, unitIdentity ]
        OccurrenceRepresentations =
            Map.ofList
                [ NodeId 0, Ok(ValueRepresentation.Scalar SettledSlot.Bool)
                  NodeId 1, Ok(ValueRepresentation.Scalar SettledSlot.Unit)
                  NodeId 2, Ok(ValueRepresentation.Scalar SettledSlot.Unit)
                  NodeId 3, Ok(ValueRepresentation.Scalar SettledSlot.Unit)
                  NodeId 4, Ok(ValueRepresentation.Scalar SettledSlot.Unit) ]
        TypeRepresentations =
            Map.ofList
                [ boolType, Ok(ValueRepresentation.Scalar SettledSlot.Bool)
                  unitIdentity, Ok(ValueRepresentation.Scalar SettledSlot.Unit) ] }

/// The unit type and branch operations have already been witnessed. Observe one
/// conditional at its Huet position; this fixture performs no graph elaboration.
let private fixture () =
    let unitIdentity = Alex.Tests.Build.unitType
    let guard = node 0 (SemanticKind.PatternBinding "condition") boolType [] None
    let thenBranch = node 1 (SemanticKind.Literal NativeLiteral.Unit) unitIdentity [] None
    let elseBranch = node 2 (SemanticKind.Literal NativeLiteral.Unit) unitIdentity [] None
    let conditional =
        node 3 (SemanticKind.IfThenElse(guard.Id, thenBranch.Id, Some elseBranch.Id)) unitIdentity [0; 1; 2] (Some 4)
    let binding = node 4 (SemanticKind.Binding("effectResult", false, false, None)) unitIdentity [3] None
    let stated = revision [guard; thenBranch; elseBranch; conditional; binding; domainNode 5; domainNode 6; domainNode 7; domainNode 8]
    let graph =
        { stated with Emission = { stated.Emission with Callable = callable; Numeric = numeric } }
        |> declareTraversalReadings
    let position = Zipper.create graph binding.Id |> require "Missing unit fixture binding" |> atChild conditional.Id
    position, thenBranch.Id, elseBranch.Id

let private unitType = TInt(IntWidth 32)
let private cellType = TMemRefStatic(1, unitType)
let private store source = MLIROp.MemRefOp(MemRefOp.Store(source, Arg 1, [Arg 4], unitType, cellType))
let private thenEffects = [store (Arg 2); store (Arg 3)]
let private elseEffects = [store (Arg 3); store (Arg 2)]

let private observe body (position: Zipper.PSGZipper) =
    let operands = MLIRAccumulator.empty ()
    let nodes, types = operands.NodeAssoc, operands.SSATypes
    let graphNodes, edges, codata = position.Graph.Nodes, position.Graph.Edges, position.Graph.Codata
    let result = matchAt (pWithUnitResult position.Focus.Id body) position 64 operands
    Assert.Same(graphNodes, position.Graph.Nodes)
    Assert.Same(edges, position.Graph.Edges)
    Assert.Same(codata, position.Graph.Codata)
    Assert.Same(nodes, operands.NodeAssoc)
    Assert.Same(types, operands.SSATypes)
    Assert.Empty(operands.AllOps)
    Assert.Empty(operands.Errors)
    result

let private conditionalResult () =
    let position, thenId, elseId = fixture ()
    let body =
        Alex.Patterns.ControlFlowPatterns.pBuildConditional
            (Arg 0) thenEffects (Some elseEffects) thenId (Some elseId) None position.Focus.Id
    match observe body position with
    | Result.Ok ((operations, TRValue result), next) ->
        Assert.Same(position.Graph, next.Graph)
        Assert.Same(position.Graph.Nodes, next.Graph.Nodes)
        Assert.Equal(position.Focus.Id, next.Focus.Id)
        Assert.Same(position.Path, next.Path)
        operations, result
    | other -> failwithf "Unit conditional did not produce a value: %A" other

[<Fact>]
let ``unit conditional preserves ordered branch effects before its sole i32 zero value`` () =
    let operations, result = conditionalResult ()
    Assert.Equal(unitType, result.Type)
    match operations with
    | [MLIROp.SCFOp(SCFOp.If(Arg 0, thenOps, Some elseOps, None));
       MLIROp.ArithOp(ArithOp.ConstI(ssa, 0L, TInt(IntWidth 32)))] ->
        Assert.Equal<MLIROp list>(thenEffects @ [MLIROp.SCFOp(SCFOp.Yield [])], thenOps)
        Assert.Equal<MLIROp list>(elseEffects @ [MLIROp.SCFOp(SCFOp.Yield [])], elseOps)
        Assert.Equal(result.SSA, ssa)
    | other -> failwithf "Conditional effects or canonical unit result were changed: %A" other

[<Fact>]
let ``unit wrapper preserves a missing operand diagnostic from its body`` () =
    let position, thenId, _ = fixture ()
    let body = parser {
        let! _ = pRecallNode thenId
        return [], TRVoid
    }
    match observe body position with
    | Result.Error message ->
        Assert.Contains($"Node {NodeId.value thenId} not yet witnessed", message)
        Assert.DoesNotContain("Unit result requires", message)
    | Result.Ok _ -> failwith "Unit wrapper masked a missing witnessed operand"

[<Fact>]
let ``unit wrapper rejects a body that already returns a value`` () =
    let position, _, _ = fixture ()
    let body = preturn ([], TRValue { SSA = Arg 0; Type = unitType })
    match observe body position with
    | Result.Error message -> Assert.Contains("Unit result requires a witnessed void operation", message)
    | Result.Ok _ -> failwith "Unit wrapper silently replaced an existing value"

[<Fact>]
let ``effectful unit conditional verifies and lowers through standard MLIR`` () =
    let operations, result = conditionalResult ()
    let parameters = [Arg 0, TInt(IntWidth 1); Arg 1, cellType; Arg 2, unitType; Arg 3, unitType; Arg 4, TIndex]
    let body = operations @ [MLIROp.FuncOp(FuncOp.Return([{ SSA = result.SSA; Type = result.Type }]))]
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("unit_effects", parameters, [result.Type], body, FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok 64) "unit_component" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.Contains("scf.if", verified)
    Assert.Contains("arith.constant 0 : i32", verified)
    let pipeline =
        "builtin.module(convert-scf-to-cf,expand-strided-metadata,memref-expand,"
        + "finalize-memref-to-llvm{index-bitwidth=64},convert-index-to-llvm{index-bitwidth=64},"
        + "convert-func-to-llvm{index-bitwidth=64},convert-arith-to-llvm{index-bitwidth=64},"
        + "convert-cf-to-llvm,reconcile-unrealized-casts)"
    let lowered = Alex.Tests.Tools.mlirOpt ["--verify-each"; "--pass-pipeline=" + pipeline] verified
    Assert.Contains("llvm.func @unit_effects", lowered)
    Assert.Contains("llvm.store", lowered)
    Assert.Contains("llvm.return", lowered)
    Assert.DoesNotContain("scf.if", lowered)
    Assert.DoesNotContain("unrealized_conversion_cast", lowered)
