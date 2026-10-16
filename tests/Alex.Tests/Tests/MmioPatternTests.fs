module Alex.Tests.MmioPatternTests

open Xunit
open Fidelity.PSG
open Alex.Dialects.Core.Types
open Alex.Dialects.Core.Serialize
open Alex.Traversal.TransferTypes
open Alex.Tests.Build

/// Direct writable borrowing is another source-owned platform operation. These
/// component rows state the public contract consumed by PlatformPatterns.
module WritableBuffer =
    let private id = NodeId
    let private support = [0;1;3;4;10;11;12;13;14;15;16;17;18;30;31;32;33] |> List.map id |> Set.ofList
    let private integer = SettledSlot.Integer(64, None)
    let private carrier site range : ScalarCarrier =
        { Site = id site; Slot = integer; Range = range; Representation = None; Declaration = None
          SourceType = intType; Obligations = []; Participants = support }
    let private fixture () =
        let declaration : BoundaryWritableBufferDeclaration =
            { Identity=id 10; Declaration=id 11; Body=id 12; Formals=[id 14;id 15]; Descriptor=id 13
              Parameter=0; CountParameter=1; BufferFormal=id 14; CountFormal=id 15
              Contract={Binding="Fixture.fill";Parameter=0;CountParameter=1
                        Hypothesis={Identity="fixture.fill";Version="1";Source="component contract"}}
              DeclarationFacts=Map.empty;Participants=support }
        let imported : BoundaryImport =
            { Identity=id 13;Binding=id 11;Scope=id 11;Library="fixture";Symbol="fill";CallingConvention="CDecl"
              DeclarationPath=[id 11];Parameters=[id 14,BoundaryScalar.WritableBytes(id 10);id 15,BoundaryScalar.Integer(64,false)]
              Result=None;Participants=support;SourceTypes=Map.empty;DeclarationFacts=Map.empty }
        let call site : BoundaryCall =
            { Site=id site;Import=id 13;Callee=id 2;Entry=None
              Arguments=[{Actual=id 0;Formal=id 14;Abi=BoundaryScalar.WritableBytes(id 10);Adaptation=None}
                         {Actual=id 1;Formal=id 15;Abi=BoundaryScalar.Integer(64,false);Adaptation=None}]
              ErasedUnitArguments=[];Result=None;ResultAdaptation=None;Resource=None;Participants=support;SourceTypes=Map.empty }
        let useRow site count storage : BoundaryWritableBufferUse =
            { Call=id site;Declaration=id 10;Parameter=0;CountParameter=1;Buffer=id 0;Count=id 1;Allocation=id 16
              Capacity=id 17;ByteFormat=id 18;CountCoverage=id count;StorageCoverage=id storage;Participants=support }
        let claim citizen kind body : ObligationInfo =
            {Id=sprintf "fixture-%d" citizen;Kind="foreign-writable-buffer-"+kind;Logic="QF_LIA"
             Statement="Source-issued component coverage";Source="component contract"
             Refs=["fixture.fill";"1";"component contract"];Body=body}
        let claims =
            [30,claim 30 "count" (ObligationBody.IntegerRepresentationCoverage(2I,2I,0I,4I))
             31,claim 31 "storage" (ObligationBody.IntegerRepresentationCoverage(0I,255I,0I,255I))
             32,claim 32 "count" (ObligationBody.IntegerRepresentationCoverage(2I,2I,0I,4I))
             33,claim 33 "storage" (ObligationBody.IntegerRepresentationCoverage(0I,255I,0I,255I))]
        let requirement : RequirementWitness =
            {Site=id 40;Condition=id 41;Diagnostic="capacity";Frontier=id 42;Continuation=id 43;PatternTest=None;Participants=[]}
        let guard : ArrayRangeGuard =
            {Requirement=id 40;Predicate=id 41;Frontier=id 42;Continuation=id 43;Count=id 17;Offset=None;Buffer=None
             Length=None;Zero=id 44;NonnegativeCount=id 45;NonnegativeOffset=None;End=None;Within=None}
        let construction : ArrayAllocationConstruction =
            {Site=id 16;Owner=id 16;Count={Actual=id 17;Binding=id 17;Reference=id 17};Default=None;Initialization=None
             Guard=guard;Participants=support}
        let allocation : MemoryArrayAllocationWitness =
            {Site=id 16;Count=id 17;CountCarrier=carrier 17 (ValueRange.Bounded(4I,4I));IndexUnsigned=true
             Element=SettledSlot.Integer(8,Some "uint8");ElementBytes=1;Alignment=1;Residence=MemoryResidence.Stack(id 11,id 11)
             MinimumCount=4I;MaximumCount=4I;Requirement=requirement;Construction=construction;Participants=support}
        let buffer = node 0 (SemanticKind.PatternBinding "buffer") (arrayOf uint8Type) [] None
        let count = node 1 (SemanticKind.PatternBinding "count") intType [] None
        let callee = node 2 (SemanticKind.PatternBinding "fill") (functionFrom (arrayOf uint8Type) (functionFrom intType unitType)) [] None
        let sites = [3;4] |> List.map(fun site->node site (SemanticKind.Application(id 2,[id 0;id 1])) unitType [2;0;1] None)
        let proofs = claims |> List.map(fun (citizen,claim)->node citizen (SemanticKind.Obligation claim) unitType [] None)
        let raw=revision (buffer::count::callee::sites@proofs)
        let boundary =
            { raw.Emission.Boundary with
                Imports=Map.ofList[id 13,imported]
                Calls=Map.ofList[id 3,call 3;id 4,call 4]
                WritableBufferDeclarations=Map.ofList[id 10,declaration]
                WritableBufferUses=Map.ofList[(id 3,0),useRow 3 30 31;(id 4,0),useRow 4 32 33] }
        let sources site = [id site;id 10;id 0;id 1;id 16;id 17;id 18]
        let graph =
            { raw with
                Obligations=List.map snd claims
                ObligationSources=Map.ofList[id 30,[sources 3];id 31,[sources 3];id 32,[sources 4];id 33,[sources 4]]
                Emission=
                    { raw.Emission with
                        Boundary=boundary
                        Numeric={raw.Emission.Numeric with Elements=Map.ofList[id 0,allocation.Element]}
                        Memory={raw.Emission.Memory with Operations=Map.ofList[id 16,MemoryWitnessOperation.ArrayAllocation allocation]} } }
            |> declareTraversalReadings
        graph,imported

    let private observe site graph =
        let operands=MLIRAccumulator.empty ()
        MLIRAccumulator.bindNode (id 0) (Arg 0) (TMemRef(TInt(IntWidth 8))) operands
        MLIRAccumulator.bindNode (id 1) (Arg 1) (TInt(IntWidth 64)) operands
        let position=focus graph graph.Nodes[id site]
        let result=matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall position 64 operands
        Assert.Empty operands.AllOps
        Assert.True((MLIRAccumulator.recallNode (id site) operands).IsNone)
        result

    /// Two source applications deliberately share actuals, but never a result
    /// citizen, context, adaptation or native SSA definition.
    let private signedFixture () =
        let graph, imported = fixture ()
        let support = Set.union support (Set.ofList ([50;51;52;53;54;55;56;60;61] |> List.map id))
        let participant group role ordinal value : Participant =
            {Node=id value;Role=role;Ordinal=ordinal;Group=id group}
        let application site context : ForeignResultApplication =
            {Declaration=imported.Binding;Call=id site;Context=[id context]
             Hypothesis=Some {Quote=id 54;Declaration=imported.Binding;Identity="fixture.result";Version="1"
                              Source="component result contract";Lower=ForeignResultBound.Constant -1I;Upper=ForeignResultBound.Argument 1}
             Arguments=[{Index=0;Node=id 0;Enclosure=ValueRange.Unbounded}
                        {Index=1;Node=id 1;Enclosure=ValueRange.Bounded(3I,3I)}]}
        let account site context logical abi : ForeignResultUse =
            {Application=application site context
             Participants=ParticipantEvidence.Established
                [participant site ParticipantRole.ForeignResultDeclaration 0 11
                 participant site ParticipantRole.ForeignResultCall 0 site
                 participant site ParticipantRole.ForeignResultContext 0 context
                 participant site ParticipantRole.ForeignResultHypothesis 0 54
                 participant site ParticipantRole.ForeignResultActual 0 0
                 participant site ParticipantRole.ForeignResultActual 1 1
                 participant site ParticipantRole.ForeignResultAbi 0 55
                 participant site ParticipantRole.ForeignResultDestination 0 56]
             Claims=[ForeignResultProofRole.LogicalCoverage,id logical;ForeignResultProofRole.AbiNarrowing,id abi]}
        let accounts=[account 3 60 50 51;account 4 61 52 53]
        let claims = accounts |> List.collect (fun account ->
            account.Claims |> List.map (fun (role,citizen) ->
                let model : ForeignResultCoverageModel =
                    {Application=account.Application;Role=role;ResultRange=ValueRange.Bounded(-1I,3I)
                     Destination=ValueRange.Bounded(-2147483648I,2147483647I);DestinationDeclaration=Some(id 56)
                     Abi=Some(id 55);AbiRange=ValueRange.Bounded(-(1I <<< 63),(1I <<< 63)-1I)
                     AbiIdentity=None;DestinationIdentity=None}
                citizen, {Id=sprintf "fixture-result-%d" (NodeId.value citizen);Kind="foreign-result-coverage";Logic="QF_LIA"
                          Statement="Source-issued conditional result coverage";Source="component result contract"
                          Refs=["fixture.result";"1";"component result contract"];Body=ObligationBody.ForeignResultCoverage model}))
        let meets = [3;4] |> List.map (fun site ->
            id site, {Consumer=id site;Operand=id site;From=64;To=32;Adapt=MeetKind.Truncate}) |> Map.ofList
        let boundary = graph.Emission.Boundary
        let calls = boundary.Calls |> Map.map (fun site call ->
            {call with Result=Some(BoundaryScalar.Integer(64,true));ResultAdaptation=Some meets[site];Participants=support})
        let sources = accounts |> List.collect (fun account ->
            match account.Participants with
            | ParticipantEvidence.Established rows -> account.Claims |> List.map (fun (_,citizen)->citizen,[rows |> List.map (fun (row: Participant) -> row.Node)])
            | _ -> failwith "Fixture requires settled source incidence")
        let nodes = claims |> List.fold (fun nodes (citizen,claim) ->
            nodes |> Map.add citizen (node (NodeId.value citizen) (SemanticKind.Obligation claim) unitType [] None)) graph.Nodes
        let graph =
            {graph with Nodes=nodes;Obligations=graph.Obligations @ List.map snd claims
                        CurrentClaims=List.fold (fun current (citizen,claim)->Map.add citizen claim current) graph.CurrentClaims claims
                        ObligationSources=List.fold (fun current (citizen,rows)->Map.add citizen rows current) graph.ObligationSources sources
                        Codata={graph.Codata with Meets=meets |> Map.map (fun _ meet -> [meet])}
                        Emission=
                            { graph.Emission with
                                Callable={graph.Emission.Callable with AliasTargets=Map.ofList [id 3,id 3;id 4,id 4]}
                                Boundary=
                                    { boundary with
                                        Calls=calls
                                        Imports=boundary.Imports.Add(imported.Identity,{imported with Result=Some(BoundaryScalar.Integer(64,true))})
                                        WritableBufferUses=boundary.WritableBufferUses |> Map.map (fun _ row->{row with Participants=support}) }
                                Numeric={graph.Emission.Numeric with ForeignResultUses=accounts} } }
        graph

    [<Fact>]
    let ``writable signed result retains two source occurrences and adapts native width`` () =
        let graph=signedFixture ()
        let rawResults = [3;4] |> List.map (fun site ->
            match observe site graph with
            | Result.Ok(([WritableBufferCall(actual,values,Some raw);ArithOp(ArithOp.TruncI(adapted,source,fromType,toType))],TRValue result),_) ->
                Assert.Equal(id site,actual)
                Assert.Equal(2,values.Length)
                Assert.Equal(TInt(IntWidth 64),raw.Type)
                Assert.Equal(raw.SSA,source)
                Assert.Equal(TInt(IntWidth 64),fromType)
                Assert.Equal(TInt(IntWidth 32),toType)
                Assert.Equal({SSA=adapted;Type=toType},result)
                Assert.Equal(NeedsTargetRealization,moduleText (Ok 64) None [WritableBufferCall(actual,values,Some raw)])
                raw.SSA
            | other -> failwithf "Writable signed result lost its original raw SSA/adaptation: %A" other)
        Assert.NotEqual(rawResults[0],rawResults[1])

    [<Theory>]
    [<InlineData("missing","unique current same-call")>]
    [<InlineData("duplicate","unique current same-call")>]
    [<InlineData("declaration","unique current same-call")>]
    [<InlineData("actual","ordered actuals")>]
    [<InlineData("hypothesis","declared hypothesis")>]
    [<InlineData("pending","pending source participants")>]
    [<InlineData("roles","distinct logical/ABI claim citizens")>]
    [<InlineData("citizen","current required logical/ABI claims")>]
    [<InlineData("context","current required logical/ABI claims")>]
    [<InlineData("support-order","current required logical/ABI claims")>]
    [<InlineData("unsupported","only void or the declared signed64")>]
    let ``writable signed result refuses withdrawn or mismatched source result evidence`` defect reason =
        let graph=signedFixture ()
        let first=graph.Emission.Numeric.ForeignResultUses.Head
        let changed =
            match defect with
            | "declaration" -> {first with Application={first.Application with Declaration=id 99}}
            | "actual" -> {first with Application={first.Application with Arguments=List.rev first.Application.Arguments}}
            | "hypothesis" -> {first with Application={first.Application with Hypothesis=None}}
            | "pending" -> {first with Participants=ParticipantEvidence.Pending {Derived=[]}}
            | "roles" -> {first with Claims=List.rev first.Claims}
            | "context" -> {first with Application={first.Application with Context=[id 61]}}
            | _ -> first
        let accounts =
            if defect="missing" then graph.Emission.Numeric.ForeignResultUses.Tail
            elif defect="duplicate" then first::graph.Emission.Numeric.ForeignResultUses
            else changed::graph.Emission.Numeric.ForeignResultUses.Tail
        let boundary=graph.Emission.Boundary
        let boundary =
            if defect="unsupported" then
                {boundary with Calls=boundary.Calls.Add(id 3,{boundary.Calls[id 3] with Result=Some(BoundaryScalar.Integer(64,false))})
                               Imports=boundary.Imports.Add(id 13,{boundary.Imports[id 13] with Result=Some(BoundaryScalar.Integer(64,false))})}
            else boundary
        let graph={graph with
                    CurrentClaims=if defect="citizen" then graph.CurrentClaims.Remove(id 51) else graph.CurrentClaims
                    ObligationSources=if defect="support-order" then graph.ObligationSources.Add(id 51,[List.rev graph.ObligationSources[id 51].Head]) else graph.ObligationSources
                    Emission={graph.Emission with Boundary=boundary;Numeric={graph.Emission.Numeric with ForeignResultUses=accounts}}}
        match observe 3 graph with
        | Result.Error message -> Assert.Contains(reason,message)
        | other -> failwithf "Invalid writable signed-result %s admitted: %A" defect other

    [<Fact>]
    let ``writable buffer retains neutral carrier ordered arguments and distinct call sites`` () =
        let graph,imported=fixture ()
        Assert.Equal<MLIRType list>([TMemRef(TInt(IntWidth 8));TInt(IntWidth 64)],BoundaryAbi.parametersIn graph.Emission.Boundary imported)
        for site in [3;4] do
            match observe site graph with
            | Result.Ok(([WritableBufferCall(actual,values,None)],TRVoid),_) ->
                Assert.Equal(id site,actual)
                Assert.Equal<Val list>([{SSA=Arg 0;Type=TMemRef(TInt(IntWidth 8))};{SSA=Arg 1;Type=TInt(IntWidth 64)}],values)
            | other -> failwithf "Writable call lost its exact account: %A" other

    [<Theory>]
    [<InlineData("missing","exact current declaration and per-use account")>]
    [<InlineData("site","native ordinal or ordered actuals")>]
    [<InlineData("ordinal","native ordinal or ordered actuals")>]
    [<InlineData("byte-format","required count/storage claim citizens")>]
    [<InlineData("claim","required count/storage claim citizens")>]
    [<InlineData("indirect","exact direct signature")>]
    [<InlineData("result","exact direct signature")>]
    let ``writable buffer refuses withdrawn or mismatched current evidence`` defect reason =
        let graph,_=fixture ()
        let boundary=graph.Emission.Boundary
        let original=boundary.WritableBufferUses[id 3,0]
        let uses =
            if defect="missing" then boundary.WritableBufferUses.Remove(id 3,0)
            else boundary.WritableBufferUses.Add((id 3,0),
                    match defect with
                    | "site" -> {original with Call=id 4}
                    | "ordinal" -> {original with Parameter=1}
                    | "byte-format" -> {original with ByteFormat=id 99}
                    | _ -> original)
        let calls =
            if defect="indirect" then boundary.Calls.Add(id 3,{boundary.Calls[id 3] with Entry=Some(id 50)})
            elif defect="result" then boundary.Calls.Add(id 3,{boundary.Calls[id 3] with Result=Some(BoundaryScalar.Integer(64,false))})
            else boundary.Calls
        let graph={graph with Emission={graph.Emission with Boundary={boundary with WritableBufferUses=uses;Calls=calls}}
                              CurrentClaims=if defect="claim" then graph.CurrentClaims.Remove(id 30) else graph.CurrentClaims}
        match observe 3 graph with
        | Result.Error message -> Assert.Contains(reason,message)
        | other -> failwithf "Invalid writable %s account admitted: %A" defect other

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    let ``writable buffer declaration and call explicitly defer portable target text`` declaration =
        let graph,imported=fixture ()
        let operation=
            if declaration then FuncOp(BoundaryFuncDecl(imported,BoundaryAbi.parametersIn graph.Emission.Boundary imported,[]))
            else WritableBufferCall(id 3,[{SSA=Arg 0;Type=TMemRef(TInt(IntWidth 8))};{SSA=Arg 1;Type=TInt(IntWidth 64)}],None)
        Assert.Equal(NeedsTargetRealization,moduleText (Ok 64) (Some "writable_component") [operation])

/// The opaque handle type of a register of the width given, as the contract states it.
let private handleType (bits: int) : TypeIdentity =
    TypeIdentity.Application(
        { Declaration = { Module = []; Name = sprintf "Mmio%d" bits }; Parameters = []; NativeKind = None }, [])

/// A write of a 16-bit value to an 8-bit register, with the meets published for the write.
/// The handle and the value are formals that were witnessed before the write.
let private registerWrite (meets: Meet list) =
    let handle = node 0 (SemanticKind.PatternBinding "register") (handleType 8) [] None
    let value = node 1 (SemanticKind.PatternBinding "value") intType [] None
    let intrinsic =
        node 2
            (SemanticKind.Intrinsic
                { Module = IntrinsicModule.Mmio; Operation = "write"
                  Category = IntrinsicCategory.Memory; FullName = "Mmio.write" })
            (functionFrom (handleType 8) (functionFrom intType unitType)) [] None
    let write = node 3 (SemanticKind.Application(intrinsic.Id, [handle.Id; value.Id])) unitType [2; 0; 1] None
    let stated = revision [handle; value; intrinsic; write]
    let graph =
        { stated with
            Codata =
                { stated.Codata with
                    Mmio = Map.ofList [ (write.Id, { Operation = "write"; Address = 1073741824I; Bits = 8; Binding = None }) ]
                    Meets = if meets.IsEmpty then Map.empty else Map.ofList [ (write.Id, meets) ] }
            Emission =
                { stated.Emission with
                    Callable =
                        { stated.Emission.Callable with
                            AliasTargets = Map.ofList [ (write.Id, write.Id) ]
                            UnitNodes = Set.singleton write.Id }
                    Numeric =
                        { stated.Emission.Numeric with
                            OccurrenceRepresentations =
                                Map.ofList [ (write.Id, Ok(ValueRepresentation.Scalar SettledSlot.Unit)) ] } } }
        |> declareTraversalReadings
    let operands = MLIRAccumulator.empty ()
    MLIRAccumulator.bindNode handle.Id (Arg 0) TIndex operands
    MLIRAccumulator.bindNode value.Id (Arg 1) (TInt(IntWidth 16)) operands
    graph, focus graph graph.Nodes[write.Id], operands, write.Id, value.Id

[<Fact>]
let ``register write adapts its value by the published meet`` () =
    let truncation consumer operand = { Consumer = consumer; Operand = operand; From = 16; To = 8; Adapt = MeetKind.Truncate }
    let _, position, operands, write, value = registerWrite [ truncation (NodeId 3) (NodeId 1) ]
    match matchAt Alex.Patterns.MmioPatterns.pMmioIntrinsic position 64 operands with
    | Result.Error message -> failwithf "The published meet was not read: %s" message
    | Result.Ok ((operations, result), _) ->
        let adapted = Alex.Traversal.Values.meetValue write 0
        let adaptation =
            operations |> List.choose (function MLIROp.ArithOp(ArithOp.TruncI _ as operation) -> Some operation | _ -> None)
            |> Assert.Single
        Assert.Equal(ArithOp.TruncI(adapted, Arg 1, TInt(IntWidth 16), TInt(IntWidth 8)), adaptation)
        let store =
            operations |> List.choose (function MLIROp.MmioStore(site, stored, address, bits) when site = write -> Some(stored, address, bits) | _ -> None)
            |> Assert.Single
        Assert.Equal((adapted, Arg 0, 8), store)
        // The write is a unit occurrence. No extension is composed.
        Assert.DoesNotContain(operations, fun operation -> match operation with MLIROp.ArithOp(ArithOp.ExtUI _) -> true | _ -> false)
        match result with
        | TRValue unit -> Assert.Equal(TInt(IntWidth 32), unit.Type)
        | other -> failwithf "The write has no unit result: %A" other
    Assert.Equal(Some(Arg 1, TInt(IntWidth 16)), MLIRAccumulator.recallNode value operands)

[<Fact>]
let ``register write without a published meet returns an error and selects no cast`` () =
    let _, position, operands, write, value = registerWrite []
    match matchAt Alex.Patterns.MmioPatterns.pMmioIntrinsic position 64 operands with
    | Result.Error message ->
        Assert.Contains(
            sprintf "Source numeric meet for consumer %d operand %d does not establish destination carrier" (NodeId.value write) (NodeId.value value),
            message)
    | Result.Ok ((operations, _), _) ->
        failwithf "A cast was selected from the widths of the operands: %A" operations
    Assert.Empty(operands.AllOps)
    Assert.Equal(None, MLIRAccumulator.recallNode write operands)

[<Theory>]
[<InlineData("%p = llvm.inttoptr %address : i64 to !llvm.ptr")>]
[<InlineData("llvm.store %v, %p : i8, !llvm.ptr")>]
[<InlineData("\"llvm.mlir.zero\"() : () -> !llvm.ptr")>]
[<InlineData("%p = custom.op : !llvm<\"ptr\">")>]
[<InlineData("\"llvm.store\" // comment\n(%v, %p) : (i8, i64) -> ()")>]
let ``portable serialization refuses LLVM dialect escape fragments`` (text: string) =
    let error = Assert.Throws<System.ArgumentException>(fun () ->
        moduleText (Ok 64) (Some "portable") [MLIROp.RawMLIR text] |> ignore)
    Assert.Contains("ALEX004", error.Message)

[<Theory>]
[<InlineData("func.func private @llvm.libraryFunction()")>]
[<InlineData("func.func private @\"llvm.libraryFunction\"()")>]
[<InlineData("// !llvm.ptr and llvm.load are data here\nfunc.func private @ordinary()")>]
[<InlineData("func.func private @ordinary() attributes {clef.note = \"!llvm.ptr\"}")>]
[<InlineData("func.func private @ordinary() attributes {clef.note = \"llvm.load\"}")>]
let ``portable serialization preserves names comments and quoted data`` (text: string) =
    match moduleText (Ok 64) None [MLIROp.RawMLIR text] with
    | Available actual -> Assert.Equal("module {\n  " + text + "\n}", actual)
    | NeedsTargetRealization -> failwith "Ordinary portable text acquired a target requirement"

let private deferredMmio =
    MLIROp.MmioLoad(NodeId 3, Alex.Traversal.Values.meetValue (NodeId 3) 0, Arg 0, 8)

[<Fact>]
let ``MMIO retains its source intent and explicitly defers target text`` () =
    Assert.Equal(NeedsTargetRealization, moduleText (Ok 64) (Some "portable") [deferredMmio])
    Assert.ThrowsAny<System.Exception>(fun () -> moduleToString (Ok 64) "portable" [deferredMmio] |> ignore)
    |> ignore

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``target deferral cannot mask a later LLVM escape inside a region`` (solver: bool) =
    let poison = MLIROp.RawMLIR "%p = llvm.mlir.zero : !llvm.ptr"
    let nested =
        if solver then MLIROp.SMTOp(SMTSolver [deferredMmio; poison])
        else MLIROp.FuncOp(FuncDef("portable", [Arg 0, TIndex], [], [deferredMmio; poison], FuncVisibility.Public))
    let error = Assert.Throws<System.ArgumentException>(fun () -> moduleText (Ok 64) (Some "portable") [nested] |> ignore)
    Assert.Contains("ALEX004", error.Message)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``portable module headers refuse LLVM syntax before target deferral`` (withMmio: bool) =
    let body = if withMmio then [deferredMmio] else []
    let error = Assert.Throws<System.ArgumentException>(fun () -> moduleText (Ok 64) (Some "unsafe { !llvm.ptr") body |> ignore)
    Assert.Contains("ALEX004", error.Message)

[<Theory>]
[<InlineData(false)>]
[<InlineData(true)>]
let ``portable function headers sanitize syntax before target deferral`` (withMmio: bool) =
    let body = if withMmio then [deferredMmio] else []
    let operation = MLIROp.FuncOp(FuncDef("unsafe() -> !llvm.ptr", [], [], body, FuncVisibility.Public))
    match moduleText (Ok 64) (Some "portable") [operation] with
    | Available actual ->
        Assert.False(withMmio)
        Assert.DoesNotContain("!llvm.ptr", actual)
        Assert.Contains("func.func @unsafe_______llvm.ptr(", actual)
    | NeedsTargetRealization -> Assert.True(withMmio)

[<Fact>]
let ``portable headers preserve LLVM named symbols`` () =
    match moduleText (Ok 64) (Some "llvm.library") [MLIROp.RawMLIR "func.func private @llvm.libraryFunction()"] with
    | Available actual -> Assert.Equal("module @llvm.library {\n  func.func private @llvm.libraryFunction()\n}", actual)
    | NeedsTargetRealization -> failwith "A portable module symbol acquired a target requirement"

[<Theory>]
[<InlineData(0, false)>]
[<InlineData(0, true)>]
[<InlineData(8, false)>]
[<InlineData(8, true)>]
let ``target deferral preserves width checking on every portable leaf`` (bits: int, beforeMmio: bool) =
    let conversion = MLIROp.ArithOp(ArithOp.TruncI(Arg 2, Arg 1, TInt(IntWidth 16), TInt(IntWidth bits)))
    let body = if beforeMmio then [conversion; deferredMmio] else [deferredMmio; conversion]
    let operation = MLIROp.FuncOp(FuncDef("portable", [], [], body, FuncVisibility.Public))
    if bits > 0 then
        Assert.Equal(NeedsTargetRealization, moduleText (Ok 64) (Some "portable") [operation])
    else
        let error = Assert.ThrowsAny<System.Exception>(fun () -> moduleText (Ok 64) (Some "portable") [operation] |> ignore)
        Assert.Contains("unresolved or nonpositive integer width", error.Message)

[<Fact>]
let ``portable hardware frame preserves declared argument names`` () =
    let ty = TInt(IntWidth 32)
    let body = [MLIROp.HWOp(HWOutput [Arg 0, ty])]
    let operation = MLIROp.HWOp(HWModule("hardware", ["input", ty], ["output", ty], body))
    Assert.Equal(
        Available "module @portable {\n  hw.module @hardware(in %input: i32, out output: i32) {\n    hw.output %input : i32\n}\n}",
        moduleText (Ok 64) (Some "portable") [operation])
