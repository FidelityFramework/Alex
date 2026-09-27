module Alex.Tests.UnionLayoutPatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Patterns.DUPatterns
open Alex.Patterns.MemoryPatterns
open Alex.Tests.Build
module Zipper = Alex.Traversal.PSGZipper

let private platform bits : PlatformWidths =
    { Register = Ok bits; Pointer = Ok bits }

// The layout the compiler service publishes for an option of a byte array under each
// platform width. The numbers are the payload offset, the size and the alignment in bytes.
let private layout bits =
    let cases = ["None", None; "Some", Some(SettledSlot.Pointer 5)]
    match bits with
    | 32 -> SettledLayout.Union(cases, Some 4, Some 24, Some 4), 24
    | 64 -> SettledLayout.Union(cases, Some 8, Some 48, Some 8), 48
    | other -> failwithf "The fixture states no union layout for a platform of %d bits" other

// The nodes and the rows are those the compiler service publishes for this fixture
// under the platform width given. The domain nodes of the publication and the rows of
// tables that no Pattern under test reads are left out. The residence is supplied by
// this fixture. It exercises witnessing and does not establish a program lifetime.
let private stated bits present =
    let payloadType = arrayOf uint8Type
    let unionType = optionOf payloadType
    let logical = node 0 (SemanticKind.PatternBinding "logical") unionType [] None
    let storage = node 1 (SemanticKind.AggregateStorage logical.Id) unionType [] None
    let payload = node 2 (SemanticKind.PatternBinding "payload") payloadType [] None
    let selected = node 3 (SemanticKind.DUInitialize(storage.Id, (if present then "Some" else "None"),
                                                   (if present then 1 else 0), (if present then Some payload.Id else None)))
                          unitType (if present then [1; 2] else [1]) None
    let held = [logical; storage; payload; selected]
    let raw = revision held
    let union, extent = layout bits
    let owned = ValueRepresentation.Buffer(Some extent, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
    let forms =
        [ logical.Id, owned
          storage.Id, owned
          payload.Id, ValueRepresentation.Buffer(None, ValueRepresentation.Scalar(SettledSlot.Integer(8, Some "uint8")))
          selected.Id, ValueRepresentation.Scalar SettledSlot.Unit ]
    let placed =
        { raw with
            Platform = platform bits
            Emission =
                { raw.Emission with
                    Numeric =
                        { raw.Emission.Numeric with
                            SourceTypes = held |> List.map (fun held -> held.Id, held.Type) |> Map.ofList
                            Layouts = Map.ofList [unionType, union]
                            OccurrenceRepresentations = forms |> List.map (fun (id, form) -> id, Ok form) |> Map.ofList } } }
    let graph = { placed with Codata = { placed.Codata with Escapes = Map.ofList [storage.Id, EscapeKind.StackScoped] } }
    graph, storage, selected

[<Theory>]
[<InlineData(32, false)>]
[<InlineData(32, true)>]
[<InlineData(64, false)>]
[<InlineData(64, true)>]
let ``union allocation and selected descriptor stores consume the source aligned layout`` bits present =
    let graph, storage, selected = stated bits present
    let operands = MLIRAccumulator.empty ()
    let focus id = Zipper.create graph id |> require "Missing union occurrence"
    let allocations, destination =
        match matchAt (pBuildAggregateStorage storage.Id) (focus storage.Id) bits operands with
        | Result.Ok ((operations, TRValue value), _) -> operations, value
        | other -> failwithf "Union allocation lost source layout: %A" other
    let word, bytes = bits / 8, 6 * (bits / 8)
    match Assert.Single allocations with
    | MLIROp.MemRefOp(MemRefOp.Alloca(_, TMemRefStatic(actualBytes, TInt(IntWidth 8)), Some alignment)) ->
        Assert.Equal(bytes, actualBytes)
        Assert.Equal(word, alignment)
    | other -> failwithf "Allocation lost source alignment: %A" other
    let descriptor = { SSA = Arg 0; Type = TMemRef(TInt(IntWidth 8)) }
    let fields = if present then [descriptor] else []
    let writes =
        match matchAt (pDUCaseAt selected.Id destination (Alex.CodeGeneration.TypeMapping.sourceTypeAt graph storage.Id) (if present then 1L else 0L) fields) (focus selected.Id) bits operands with
        | Result.Ok ((operations, TRVoid), _) -> operations
        | other -> failwithf "Selected union initialization failed: %A" other
    let views = writes |> List.choose (function
        | MLIROp.MemRefOp(MemRefOp.View(_, _, offset, _, _)) -> Some offset
        | _ -> None)
    if present then
        let offset = Assert.Single views
        Assert.Contains(writes, function MLIROp.ArithOp(ArithOp.ConstI(actual, value, TIndex)) -> actual = offset && value = int64 word | _ -> false)
    else Assert.Empty views
    let stores = writes |> List.filter (function MLIROp.MemRefOp(MemRefOp.StoreAligned _) -> true | _ -> false)
    Assert.Equal((if present then 2 else 1), stores.Length)
    let definition = MLIROp.FuncOp(FuncOp.FuncDef("initialize_aligned_union", [descriptor.SSA, descriptor.Type], [],
        allocations @ writes @ [MLIROp.FuncOp(FuncOp.Return [])], FuncVisibility.Public))
    let text = Alex.Dialects.Core.Serialize.moduleToString (Ok bits) "union_layout_component" [definition]
    let verified = Alex.Tests.Tools.mlirOpt ["--verify-each"] text
    Assert.DoesNotContain("memref.load", verified)
    Assert.Equal((if present then 2 else 1), verified.Split("memref.store").Length - 1)
