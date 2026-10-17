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
    let private fixture posix =
        let support = if posix then support |> Set.add (id 5) |> Set.add (id 19) else support
        let bufferParameter, countParameter = if posix then 1, 2 else 0, 1
        let formals = if posix then [id 19;id 14;id 15] else [id 14;id 15]
        let fdMeet site = {Consumer=id site;Operand=id 5;From=64;To=32;Adapt=MeetKind.Truncate}
        let declaration : BoundaryWritableBufferDeclaration =
            { Identity=id 10; Declaration=id 11; Body=id 12; Formals=formals; Descriptor=id 13
              Parameter=bufferParameter; CountParameter=countParameter; BufferFormal=id 14; CountFormal=id 15
              Contract={Binding="Fixture.fill";Parameter=bufferParameter;CountParameter=countParameter
                        Hypothesis={Identity="fixture.fill";Version="1";Source="component contract"}}
              DeclarationFacts=Map.empty;Participants=support }
        let imported : BoundaryImport =
            { Identity=id 13;Binding=id 11;Scope=id 11;Library="fixture";Symbol="fill";CallingConvention="CDecl"
              DeclarationPath=[id 11];Parameters=[id 14,BoundaryScalar.WritableBytes(id 10);id 15,BoundaryScalar.Integer(64,false)]
              Result=None;Participants=support;SourceTypes=Map.empty;DeclarationFacts=Map.empty }
        let imported =
            if posix then {imported with Parameters=(id 19,BoundaryScalar.Integer(32,true))::imported.Parameters}
            else imported
        let call site : BoundaryCall =
            { Site=id site;Import=id 13;Callee=id 2;Entry=None
              Arguments=[{Actual=id 0;Formal=id 14;Abi=BoundaryScalar.WritableBytes(id 10);Adaptation=None;OptionalEntry=None}
                         {Actual=id 1;Formal=id 15;Abi=BoundaryScalar.Integer(64,false);Adaptation=None;OptionalEntry=None}]
              ErasedUnitArguments=[];Result=None;ResultAdaptation=None;Resource=None;Participants=support;SourceTypes=Map.empty }
        let call site =
            let original = call site
            if posix then
                {original with Arguments={Actual=id 5;Formal=id 19;Abi=BoundaryScalar.Integer(32,true);Adaptation=Some(fdMeet site);OptionalEntry=None}::original.Arguments}
            else original
        let useRow site count storage : BoundaryWritableBufferUse =
            { Call=id site;Declaration=id 10;Parameter=bufferParameter;CountParameter=countParameter;Buffer=id 0;Count=id 1;Allocation=id 16
              Capacity=id 17;ByteFormat=id 18;CountCoverage=id count;StorageCoverage=id storage;Participants=support }
        let claim citizen kind body : ObligationInfo =
            {Id=sprintf "fixture-%d" citizen;Kind="foreign-writable-buffer-"+kind;Logic="QF_LIA"
             Statement="Source-issued component coverage";Source="component contract"
             Refs=["fixture.fill";"1";"component contract"];Body=body}
        let countValue = if posix then 3I else 2I
        let claims =
            [30,claim 30 "count" (ObligationBody.IntegerRepresentationCoverage(countValue,countValue,0I,4I))
             31,claim 31 "storage" (ObligationBody.IntegerRepresentationCoverage(0I,255I,0I,255I))
             32,claim 32 "count" (ObligationBody.IntegerRepresentationCoverage(countValue,countValue,0I,4I))
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
        let calleeType = functionFrom (arrayOf uint8Type) (functionFrom intType unitType)
        let callee = node 2 (SemanticKind.PatternBinding "fill") (if posix then functionFrom intType calleeType else calleeType) [] None
        let actuals = if posix then [5;0;1] else [0;1]
        let sites = [3;4] |> List.map(fun site->node site (SemanticKind.Application(id 2,List.map id actuals)) unitType (2::actuals) None)
        let proofs = claims |> List.map(fun (citizen,claim)->node citizen (SemanticKind.Obligation claim) unitType [] None)
        let nodes = buffer::count::callee::sites@proofs
        let raw=revision (if posix then node 5 (SemanticKind.PatternBinding "fd") intType [] None::nodes else nodes)
        let boundary =
            { raw.Emission.Boundary with
                Imports=Map.ofList[id 13,imported]
                Calls=Map.ofList[id 3,call 3;id 4,call 4]
                WritableBufferDeclarations=Map.ofList[id 10,declaration]
                WritableBufferUses=Map.ofList[(id 3,bufferParameter),useRow 3 30 31;(id 4,bufferParameter),useRow 4 32 33] }
        let sources site = [id site;id 10;id 0;id 1;id 16;id 17;id 18]
        let graph =
            { raw with
                Obligations=List.map snd claims
                Codata={raw.Codata with Meets=if posix then Map.ofList [id 3,[fdMeet 3];id 4,[fdMeet 4]] else Map.empty}
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
        if graph.Nodes.ContainsKey(id 5) then
            MLIRAccumulator.bindNode (id 5) (Arg 2) (TInt(IntWidth 64)) operands
        let position=focus graph graph.Nodes[id site]
        let result=matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall position 64 operands
        Assert.Empty operands.AllOps
        Assert.True((MLIRAccumulator.recallNode (id site) operands).IsNone)
        result

    /// Two source applications deliberately share actuals, but never a result
    /// citizen, context, adaptation or native SSA definition.
    let private signedFixture posix =
        let graph, imported = fixture posix
        let support = Set.union imported.Participants (Set.ofList ([50;51;52;53;54;55;56;60;61] |> List.map id))
        let participant group role ordinal value : Participant =
            {Node=id value;Role=role;Ordinal=ordinal;Group=id group}
        let application site context : ForeignResultApplication =
            {Declaration=imported.Binding;Call=id site;Context=[id context]
             Hypothesis=Some {Quote=id 54;Declaration=imported.Binding;Identity="fixture.result";Version="1"
                              Source="component result contract";Lower=ForeignResultBound.Constant -1I;Upper=ForeignResultBound.Argument(if posix then 2 else 1)}
             Arguments=graph.Emission.Boundary.Calls[id site].Arguments |> List.mapi(fun index operand ->
                 {Index=index;Node=operand.Actual;Enclosure=if operand.Actual=id 1 then ValueRange.Bounded(3I,3I) else ValueRange.Unbounded})}
        let account site context logical abi : ForeignResultUse =
            {Application=application site context
             Participants=ParticipantEvidence.Established(
                [participant site ParticipantRole.ForeignResultDeclaration 0 11
                 participant site ParticipantRole.ForeignResultCall 0 site
                 participant site ParticipantRole.ForeignResultContext 0 context
                 participant site ParticipantRole.ForeignResultHypothesis 0 54]
                @ (graph.Emission.Boundary.Calls[id site].Arguments |> List.mapi(fun ordinal operand ->
                    participant site ParticipantRole.ForeignResultActual ordinal (NodeId.value operand.Actual)))
                @ [participant site ParticipantRole.ForeignResultAbi 0 55
                   participant site ParticipantRole.ForeignResultDestination 0 56])
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
                        Codata={graph.Codata with Meets=meets |> Map.map (fun site meet -> (graph.Codata.Meets.TryFind site |> Option.defaultValue []) @ [meet])}
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
        let graph=signedFixture false
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

    /// These component rows exercise exact published adaptation replay. The
    /// source-to-native test owns how a source fd obtains its native carrier.
    [<Fact>]
    let ``POSIX writable buffer retains scalar buffer count order and exact fd adaptation`` () =
        let graph=signedFixture true
        let imported=graph.Emission.Boundary.Imports[id 13]
        Assert.Equal<MLIRType list>(
            [TInt(IntWidth 32);TMemRef(TInt(IntWidth 8));TInt(IntWidth 64)],
            BoundaryAbi.parametersIn graph.Emission.Boundary imported)
        let rawResults = [3;4] |> List.map(fun site ->
            match observe site graph with
            | Result.Ok(([ArithOp(ArithOp.TruncI(fd,fdSource,fdFrom,fdTo));
                          WritableBufferCall(actual,values,Some raw);
                          ArithOp(ArithOp.TruncI(adapted,source,fromType,toType))],TRValue result),_) ->
                Assert.Equal(id site,actual)
                Assert.Equal(Arg 2,fdSource)
                Assert.Equal(TInt(IntWidth 64),fdFrom)
                Assert.Equal(TInt(IntWidth 32),fdTo)
                Assert.Equal<Val list>(
                    [{SSA=fd;Type=fdTo};{SSA=Arg 0;Type=TMemRef(TInt(IntWidth 8))};{SSA=Arg 1;Type=TInt(IntWidth 64)}],values)
                Assert.Equal(TInt(IntWidth 64),raw.Type)
                Assert.Equal(raw.SSA,source)
                Assert.Equal(TInt(IntWidth 64),fromType)
                Assert.Equal(TInt(IntWidth 32),toType)
                Assert.Equal({SSA=adapted;Type=toType},result)
                Assert.Equal(NeedsTargetRealization,moduleText (Ok 64) None [WritableBufferCall(actual,values,Some raw)])
                raw.SSA
            | other -> failwithf "POSIX writable call lost its ordered native vector or published adaptation: %A" other)
        Assert.NotEqual(rawResults[0],rawResults[1])

    [<Theory>]
    [<InlineData("actual-order","exact direct signature and complete ordered actuals")>]
    [<InlineData("count-ordinal","native ordinal or ordered actuals")>]
    [<InlineData("fd-meet-missing","exact source numeric meet")>]
    [<InlineData("fd-meet-changed","exact source numeric meet")>]
    [<InlineData("fd-adaptation-missing","exact source numeric meet")>]
    let ``POSIX writable buffer refuses changed actual order or current fd adaptation`` defect reason =
        let graph=signedFixture true
        let boundary=graph.Emission.Boundary
        let original=boundary.Calls[id 3]
        let call =
            if defect="actual-order" then {original with Arguments=List.rev original.Arguments}
            elif defect="fd-adaptation-missing" then
                let arguments = original.Arguments |> List.map(fun operand ->
                    if operand.Actual=id 5 then {operand with Adaptation=None} else operand)
                {original with Arguments=arguments}
            else original
        let uses =
            if defect="count-ordinal" then
                boundary.WritableBufferUses.Add((id 3,1),{boundary.WritableBufferUses[id 3,1] with CountParameter=1})
            else boundary.WritableBufferUses
        let meets = graph.Codata.Meets[id 3] |> List.choose(fun meet ->
            if meet.Operand<>id 5 then Some meet
            elif defect="fd-meet-missing" then None
            elif defect="fd-meet-changed" then Some {meet with From=32}
            else Some meet)
        let graph={graph with
                    Codata={graph.Codata with Meets=graph.Codata.Meets.Add(id 3,meets)}
                    Emission={graph.Emission with Boundary={boundary with Calls=boundary.Calls.Add(id 3,call);WritableBufferUses=uses}}}
        match observe 3 graph with
        | Result.Error message -> Assert.Contains(reason,message)
        | other -> failwithf "Invalid POSIX writable %s evidence admitted: %A" defect other

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
        let graph=signedFixture false
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
        let graph,imported=fixture false
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
        let graph,_=fixture false
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
        let graph,imported=fixture false
        let operation=
            if declaration then FuncOp(BoundaryFuncDecl(imported,BoundaryAbi.parametersIn graph.Emission.Boundary imported,[]))
            else WritableBufferCall(id 3,[{SSA=Arg 0;Type=TMemRef(TInt(IntWidth 8))};{SSA=Arg 1;Type=TInt(IntWidth 64)}],None)
        Assert.Equal(NeedsTargetRealization,moduleText (Ok 64) (Some "writable_component") [operation])

/// Component rows consumed by the existing published-memory owner. Source
/// admission and complete returned-arm proofs are exercised in the source repo.
module ReturnedCheckedText =
    let private id = NodeId
    let private byte = SettledSlot.Integer(8,Some "octet")
    let private bytes = ValueRepresentation.Buffer(None,ValueRepresentation.Scalar byte)
    let private optionType = optionOf stringType
    let private optionRepresentation = ValueRepresentation.Union(["ValueNone",[];"ValueSome",[bytes]],Some(8,32,8))
    let private nativeCarrier = TMemRefStatic(32,TInt(IntWidth 8))
    let private support = [1..50] |> List.map id |> Set.ofList
    let private carrier site range : ScalarCarrier =
        {Site=id site;Slot=SettledSlot.Integer(32,None);Range=range;Representation=None;Declaration=None
         SourceType=intType;Obligations=[];Participants=support}
    let private fixtureWithSnapshot snapshot owner =
        let life : MemoryCheckedResultLifetime =
            {Application=id 9;Callee=id 18;Declaration=id 19;Implementation=id 17;Argument=id 21;Formal=id 23
             Body=id 3;Caller=id 24;Actual=id 20;Elimination=id 25;SomeUse=id 11;NoneUse=id 12
             SomeBackingRetirement=id 13;SomeCarrierRetirement=id 14;NoneCarrierRetirement=id 15
             Uses=[id 9;id 20;id 10;id 11;id 12;id 13;id 14;id 15]
             Policy={ProjectPath="fixture.fidproj";SourceVersion="component-policy";Model="Standard"}
             Platform=id 33;Space=id 34;MaximumLiveBytes=35L;Capacity=id 32}
        let construction : CheckedStringConstruction =
            {Owner=id 3;Input=id 21;Snapshot=id snapshot;Length=id 2;Validation=id 4;Decision=id 26;Text=id 5
             Success=id 6;Failure=id 7;Retirement=id 8;Validator="RFC3629-v1";Returned=Some life}
        let requirement : RequirementWitness =
            {Site=id 35;Condition=id 36;Diagnostic="capacity";Frontier=id 37;Continuation=id 38;PatternTest=None;Participants=[]}
        let guard : ArrayRangeGuard =
            {Requirement=id 35;Predicate=id 36;Frontier=id 37;Continuation=id 38;Count=id 2;Offset=None
             Buffer=None;Length=None;Zero=id 39;NonnegativeCount=id 41;NonnegativeOffset=None;End=None;Within=None}
        let allocation : MemoryArrayAllocationWitness =
            {Site=id 1;Count=id 2;CountCarrier=carrier 2 (ValueRange.Bounded(3I,3I));IndexUnsigned=true;Element=byte
             ElementBytes=1;Alignment=16;Residence=MemoryResidence.Heap(life.Application,life.Space)
             MinimumCount=3I;MaximumCount=3I;Requirement=requirement
             Construction={Site=id 1;Owner=id owner;Count={Actual=id 2;Binding=id 2;Reference=id 2};Default=None;Initialization=None;Guard=guard;Participants=support}
             Participants=support}
        let copy : MemoryArrayCopyWitness =
            {Site=id 40;Source=id 21;SourceOffset=id 39;Destination=id 1;DestinationOffset=id 39
             Count=id 2;CountCarrier=allocation.CountCarrier;CountOperand=allocation.Construction.Count
             Allocation=Some(id 1);Loop=None;Read=None;Write=None;Requirements=[];Participants=support}
        let validation : MemoryUtf8ValidationWitness =
            {Site=id 4;Construction=construction;Copy=copy;Storage=MemoryCheckedSnapshotStorage.Allocated allocation;SourceCarrier=bytes}
        let extent : MemoryExtentWitness =
            {Site=id 11;Source=id 10;Element={Name="octet";Capability="native";Family="uint";Bits=8;MinMagnitude="0";MaxMagnitude="255";Boundary="exact"}
             ElementDeclaration=id 42;Result=carrier 11 (ValueRange.Bounded(3I,3I));IndexUnsigned=true
             Extent={Site=id 11;Source=id 10;ExtentSource=id 10;StaticOrigins=Map.empty;Participants=ParticipantEvidence.Established []}
             Participants=support}
        let constructed site : MemoryConstructedValueWitness =
            {Site=id site;Owner=id 3;SourceType=optionType;Residence=allocation.Residence;Uses=Set.empty
             Construction=construction;Platform=life.Platform;Layout=id 31;Capacity=id 46}
        let retirement site value target : MemoryWitnessOperation =
            MemoryWitnessOperation.CheckedResultRetirement {Site=id site;Value=id value;Target=target;Construction=construction}
        let operations =
            [id 1,MemoryWitnessOperation.ArrayAllocation allocation
             id 4,MemoryWitnessOperation.Utf8Validation validation
             id 6,MemoryWitnessOperation.ConstructedValue(constructed 6)
             id 7,MemoryWitnessOperation.ConstructedValue(constructed 7)
             id 8,MemoryWitnessOperation.SnapshotRetirement {Site=id 8;Construction=construction;Storage=MemoryCheckedSnapshotStorage.Allocated allocation}
             id 11,MemoryWitnessOperation.BufferExtent extent
             id 13,retirement 13 10 MemoryCheckedRetirementTarget.Backing
             id 14,retirement 14 20 MemoryCheckedRetirementTarget.Carrier
             id 15,retirement 15 20 MemoryCheckedRetirementTarget.Carrier] |> Map.ofList
        let nodes = [1,arrayOf uint8Type;2,intType;3,optionType;4,boolType;5,stringType;6,optionType;7,optionType;8,unitType
                     9,optionType;10,stringType;11,intType;12,intType;13,unitType;14,unitType;15,unitType;16,stringType;20,optionType;22,optionType]
                    |> List.map(fun (site,ty)->node site (SemanticKind.PatternBinding(sprintf "value%d" site)) ty [] None)
        let raw = revision nodes
        let representations = [1,bytes;4,ValueRepresentation.Scalar SettledSlot.Bool;5,bytes;6,optionRepresentation;7,optionRepresentation
                               9,optionRepresentation;10,bytes;16,bytes;20,optionRepresentation;22,optionRepresentation]
                              |> List.map(fun (site,representation)->id site,Ok representation) |> Map.ofList
        let capacity citizen bytes : ObligationInfo =
            {Id=sprintf "fixture-capacity-%d" citizen;Kind="memory-capacity";Logic="QF_LIA"
             Statement="Source-issued checked capacity";Source="component contract";Refs=[]
             Body=ObligationBody.CapacityFits(bytes,4096L)}
        let claims=Map.ofList[id 32,capacity 32 35L;id 46,capacity 46 32L]
        { raw with
            Nodes=claims |> Map.fold(fun nodes citizen info ->
                nodes.Add(citizen,node (NodeId.value citizen) (SemanticKind.Obligation info) unitType [] None)) raw.Nodes
            CurrentClaims=claims
            Obligations=claims.Values |> Seq.toList
            ObligationSources=Map.ofList[id 32,[Set.toList support];id 46,[Set.toList support]]
            Emission=
                { raw.Emission with
                    Callable={raw.Emission.Callable with AliasTargets=nodes |> List.map(fun node->node.Id,node.Id) |> Map.ofList}
                    Numeric=
                        { raw.Emission.Numeric with
                            SourceTypes=nodes |> List.map(fun node->node.Id,node.Type) |> Map.ofList
                            OccurrenceRepresentations=representations
                            Layouts=Map.ofList [optionType,SettledLayout.Union(["ValueNone",None;"ValueSome",Some(SettledSlot.InlineBytes(24,8))],Some 8,Some 32,Some 8)] }
                    Memory={raw.Emission.Memory with Operations=operations;ArrayCopies=Map.ofList[id 40,copy]} } }
        |> declareTraversalReadings

    let private fixture () = fixtureWithSnapshot 1 1

    let private observe site graph physical =
        let operands=MLIRAccumulator.empty ()
        for value,ssa,ty in [1,Arg 4,TMemRef(TInt(IntWidth 8));2,Arg 3,TInt(IntWidth 32);
                            10,Arg 1,TMemRef(TInt(IntWidth 8));16,Arg 5,TMemRef(TInt(IntWidth 8));
                            20,Arg 0,nativeCarrier;22,Arg 2,nativeCarrier] do
            MLIRAccumulator.bindNode (id value) ssa ty operands
        let operands=physical operands
        let result=matchAt Alex.Patterns.MemoryPatterns.pPublishedMemoryOperation (focus graph graph.Nodes[id site]) 64 operands
        Assert.Empty operands.AllOps
        result

    [<Fact>]
    let ``allocated checked snapshot validation preserves parser success`` () =
        let graph=fixture ()
        let memory=graph.Emission.Memory
        let validation=match memory.Operations[id 4] with MemoryWitnessOperation.Utf8Validation row->row | _->failwith "fixture"
        let representation=match memory.Operations[id 11] with MemoryWitnessOperation.BufferExtent row->row.Element | _->failwith "fixture"
        let view : MemoryStringViewWitness =
            {Site=id 5;Source=validation.Construction.Snapshot;Owner=validation.Construction.Owner
             Snapshot=validation.Construction.Snapshot;Direction=MemoryStringViewDirection.FromBytes
             Checked=Some validation.Construction;SourceCarrier=bytes;ResultCarrier=bytes;Element=byte
             Representation=representation;Declaration=id 42;Extent=validation.Copy.CountCarrier;Participants=support}
        let graph={graph with Emission={graph.Emission with Memory={memory with Operations=memory.Operations.Add(id 5,MemoryWitnessOperation.StringView view)}}}
        match observe 4 graph (fun accumulator->accumulator) with
        | Ok(([Utf8Validate(site,snapshot,result)],[],TRValue actual),_) ->
            Assert.Equal(id 4,site)
            Assert.Equal(Arg 4,snapshot.SSA)
            Assert.Equal(TInt(IntWidth 1),result.Type)
            Assert.Equal(result,actual)
        | other -> failwithf "Allocated validation lost its successful parser continuation: %A" other

    [<Theory>]
    [<InlineData(6)>]
    [<InlineData(7)>]
    let ``returned checked outcome allocates its published aligned carrier`` site =
        let graph=fixture ()
        let operands=MLIRAccumulator.empty ()
        let result=matchAt (Alex.Patterns.MemoryPatterns.pAllocValue (id site) (Arg 7) nativeCarrier) (focus graph graph.Nodes[id site]) 64 operands
        match result with
        | Ok(MemRefOp(AllocStatic(Arg 7,actual,Some 8)),_) -> Assert.Equal(nativeCarrier,actual)
        | other -> failwithf "Returned outcome lost aligned heap storage: %A" other

    [<Fact>]
    let ``returned snapshot owner joins distinct emitted allocation site`` () =
        let graph=fixtureWithSnapshot 43 43
        let operands=MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.MemoryPatterns.pAllocValue (id 6) (Arg 7) nativeCarrier) (focus graph graph.Nodes[id 6]) 64 operands with
        | Ok(MemRefOp(AllocStatic(Arg 7,actual,Some 8)),_) -> Assert.Equal(nativeCarrier,actual)
        | other -> failwithf "Published outer snapshot owner was conflated with emitted allocation site: %A" other

    [<Fact>]
    let ``returned snapshot owner refuses changed construction owner`` () =
        let graph=fixtureWithSnapshot 43 44
        let operands=MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.MemoryPatterns.pAllocValue (id 6) (Arg 7) nativeCarrier) (focus graph graph.Nodes[id 6]) 64 operands with
        | Result.Error reason -> Assert.Contains("original snapshot construction occurrence",reason)
        | Ok _ -> failwith "Changed snapshot construction owner admitted"
        Assert.True((MLIRAccumulator.recallSSAType (Arg 7) operands).IsNone)

    [<Fact>]
    let ``returned snapshot owner refuses changed current allocation row`` () =
        let graph=fixtureWithSnapshot 43 43
        let memory=graph.Emission.Memory
        let original=match memory.Operations[id 1] with MemoryWitnessOperation.ArrayAllocation row->row | _->failwith "fixture"
        let graph={graph with Emission={graph.Emission with Memory={memory with Operations=memory.Operations.Add(id 1,MemoryWitnessOperation.ArrayAllocation {original with Alignment=8})}}}
        let operands=MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.MemoryPatterns.pAllocValue (id 6) (Arg 7) nativeCarrier) (focus graph graph.Nodes[id 6]) 64 operands with
        | Result.Error reason -> Assert.Contains("current heap snapshot allocation",reason)
        | Ok _ -> failwith "Withdrawn current allocation row admitted"
        Assert.True((MLIRAccumulator.recallSSAType (Arg 7) operands).IsNone)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    let ``returned snapshot owner keeps carrier and combined capacity citizens distinct`` combined =
        let graph=fixtureWithSnapshot 43 43
        let citizen=id(if combined then 32 else 46)
        let changed={graph.CurrentClaims[citizen] with Body=ObligationBody.CapacityFits((if combined then 32L else 35L),4096L)}
        let graph={graph with CurrentClaims=graph.CurrentClaims.Add(citizen,changed)
                              Obligations=graph.Obligations |> List.map(fun info->if info.Id=changed.Id then changed else info)}
        let operands=MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.MemoryPatterns.pAllocValue (id 6) (Arg 7) nativeCarrier) (focus graph graph.Nodes[id 6]) 64 operands with
        | Result.Error reason -> Assert.Contains((if combined then "combined live-byte capacity citizen" else "per-instance capacity citizen"),reason)
        | Ok _ -> failwith "Distinct capacity proof roles were conflated"
        Assert.True((MLIRAccumulator.recallSSAType (Arg 7) operands).IsNone)

    [<Theory>]
    [<InlineData(13,1)>]
    [<InlineData(14,0)>]
    [<InlineData(15,0)>]
    [<InlineData(8,4)>]
    let ``returned checked retirement deallocates only the recalled actual instance`` site argument =
        match observe site (fixture ()) (fun value -> value) with
        | Ok(([MemRefOp(Dealloc(actual,_))],[],TRVoid),_) -> Assert.Equal(Arg argument,actual)
        | other -> failwithf "Returned retirement lost its exact caller or helper actual: %A" other

    [<Fact>]
    let ``returned checked snapshot retains runtime count and published alignment`` () =
        match observe 1 (fixture ()) (fun value -> value) with
        | Ok(([IndexOp _;MemRefOp(Alloc(_,_,TInt(IntWidth 8),Some 16)) as operation],[],TRValue _),_) ->
            match moduleText (Ok 64) None [operation] with
            | Available text -> Assert.Contains("{alignment = 16 : i64}",text)
            | NeedsTargetRealization -> failwith "Neutral allocation must retain portable text"
        | other -> failwithf "Returned snapshot lost its allocation alignment: %A" other

    [<Fact>]
    let ``returned checked changes preserve local empty stack retirement`` () =
        let graph=fixture ()
        let memory=graph.Emission.Memory
        let retired=match memory.Operations[id 8] with MemoryWitnessOperation.SnapshotRetirement row->row | _->failwith "fixture"
        let construction={retired.Construction with Returned=None}
        let allocated=match retired.Storage with MemoryCheckedSnapshotStorage.Allocated allocation->allocation | _->failwith "fixture"
        let allocation={allocated with MinimumCount=0I;MaximumCount=0I;Residence=MemoryResidence.Stack(id 17,id 34)}
        let operations=memory.Operations
                        |> Map.add (id 1) (MemoryWitnessOperation.ArrayAllocation allocation)
                        |> Map.add (id 4) (MemoryWitnessOperation.Utf8Validation {Site=id 4;Construction=construction;Storage=MemoryCheckedSnapshotStorage.Allocated allocation;Copy=memory.ArrayCopies[id 40];SourceCarrier=bytes})
                        |> Map.add (id 8) (MemoryWitnessOperation.SnapshotRetirement {Site=id 8;Construction=construction;Storage=MemoryCheckedSnapshotStorage.Allocated allocation})
        let graph={graph with Emission={graph.Emission with Memory={memory with Operations=operations}}}
        match observe 8 graph (fun value->value) with
        | Ok(([Utf8SnapshotRetire(_,value)],[],TRVoid),_) -> Assert.Equal(Arg 4,value.SSA)
        | other -> failwithf "Local empty stack retirement changed: %A" other

    [<Fact>]
    let ``returned checked retirement refuses a changed physical caller carrier`` () =
        let physical accumulator =
            MLIRAccumulator.registerSSAType (Arg 0) (TMemRefStatic(31,TInt(IntWidth 8))) accumulator
            accumulator
        match observe 14 (fixture ()) physical with
        | Result.Error reason -> Assert.Contains("exact registered physical caller value",reason)
        | Ok _ -> failwith "Changed physical caller carrier was retired"

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("application")>]
    [<InlineData("space")>]
    [<InlineData("zero")>]
    [<InlineData("stack")>]
    let ``returned checked carrier refuses absent or changed heap lifetime`` defect =
        let graph=fixture ()
        let operations=graph.Emission.Memory.Operations
        let allocation=match operations[id 6] with MemoryWitnessOperation.ConstructedValue row->row | _->failwith "fixture"
        let life=allocation.Construction.Returned.Value
        let construction={allocation.Construction with Returned=if defect="missing" then None else Some life}
        let allocation={allocation with Construction=construction
                                        Residence=match defect with "application"->MemoryResidence.Heap(id 99,life.Space) | "space"->MemoryResidence.Heap(life.Application,id 99) | "stack"->MemoryResidence.Stack(id 17,life.Space) | _->allocation.Residence}
        let operations=operations.Add(id 6,MemoryWitnessOperation.ConstructedValue allocation)
        let operations =
            if defect="zero" then
                operations |> Map.map(fun _ operation ->
                    match operation with
                    | MemoryWitnessOperation.ArrayAllocation row -> MemoryWitnessOperation.ArrayAllocation {row with MinimumCount=0I}
                    | MemoryWitnessOperation.Utf8Validation row ->
                        match row.Storage with
                        | MemoryCheckedSnapshotStorage.Allocated allocation -> MemoryWitnessOperation.Utf8Validation {row with Storage=MemoryCheckedSnapshotStorage.Allocated {allocation with MinimumCount=0I}}
                        | _ -> operation
                    | _ -> operation)
            else operations
        let graph={graph with Emission={graph.Emission with Memory={graph.Emission.Memory with Operations=operations}}}
        let operands=MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.MemoryPatterns.pAllocValue (id 6) (Arg 7) nativeCarrier) (focus graph graph.Nodes[id 6]) 64 operands with
        | Result.Error reason -> Assert.Contains((if defect="zero" then "positive-count" elif defect="stack" then "local stack residence" else "exact source application"),reason)
        | Ok _ -> failwithf "Changed returned heap %s admitted" defect
        Assert.Empty operands.AllOps
        Assert.True((MLIRAccumulator.recallSSAType (Arg 7) operands).IsNone)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    let ``returned checked retirement refuses a same typed foreign actual`` backing =
        let graph=fixture ()
        let site=if backing then 13 else 14
        let memory=graph.Emission.Memory
        let retirement=match memory.Operations[id site] with MemoryWitnessOperation.CheckedResultRetirement row->row | _->failwith "fixture"
        let retirement={retirement with Value=id(if backing then 16 else 22)}
        let graph={graph with Emission={graph.Emission with Memory={memory with Operations=memory.Operations.Add(id site,MemoryWitnessOperation.CheckedResultRetirement retirement)}}}
        match observe site graph (fun value -> value) with
        | Result.Error reason -> Assert.Contains("exact caller value or cleanup occurrence",reason)
        | Ok _ -> failwith "A foreign same-typed value was retired"

    /// The existing checked-memory test owner keeps empty and allocated rows
    /// distinct. No literal/global or source compiler is manufactured here.
    module EmptySnapshots =
        let private emptyFixture () =
            let graph=fixtureWithSnapshot 43 43
            let memory=graph.Emission.Memory
            let original=match memory.Operations[id 4] with MemoryWitnessOperation.Utf8Validation row->row | _->failwith "fixture"
            let life={original.Construction.Returned.Value with MaximumLiveBytes=32L}
            let construction={original.Construction with Returned=Some life}
            let empty : MemoryEmptySnapshotWitness =
                {Site=id 1;Snapshot=id 43;Owner=id 3;Count=id 2;SourceType=arrayOf uint8Type;Declaration=id 42}
            let count={original.Copy.CountCarrier with Range=ValueRange.Bounded(0I,0I)}
            let copy={original.Copy with CountCarrier=count}
            let representation=match memory.Operations[id 11] with MemoryWitnessOperation.BufferExtent row->row.Element | _->failwith "fixture"
            let view : MemoryStringViewWitness =
                {Site=id 5;Source=id 43;Owner=id 3;Snapshot=id 43;Direction=MemoryStringViewDirection.FromBytes
                 Checked=Some construction;SourceCarrier=bytes;ResultCarrier=bytes;Element=byte;Representation=representation
                 Declaration=id 42;Extent=count;Participants=support}
            let operations=memory.Operations |> Map.map(fun _ operation ->
                match operation with
                | MemoryWitnessOperation.ArrayAllocation _ -> MemoryWitnessOperation.EmptySnapshot empty
                | MemoryWitnessOperation.Utf8Validation row -> MemoryWitnessOperation.Utf8Validation {row with Construction=construction;Storage=MemoryCheckedSnapshotStorage.Empty empty;Copy=copy}
                | MemoryWitnessOperation.ConstructedValue row -> MemoryWitnessOperation.ConstructedValue {row with Construction=construction}
                | MemoryWitnessOperation.SnapshotRetirement row -> MemoryWitnessOperation.SnapshotRetirement {row with Construction=construction;Storage=MemoryCheckedSnapshotStorage.Empty empty}
                | MemoryWitnessOperation.CheckedResultRetirement row -> MemoryWitnessOperation.CheckedResultRetirement {row with Construction=construction;Target=if row.Target=MemoryCheckedRetirementTarget.Backing then MemoryCheckedRetirementTarget.EmptyBacking else row.Target}
                | MemoryWitnessOperation.BufferExtent row -> MemoryWitnessOperation.BufferExtent {row with Result={row.Result with Range=ValueRange.Bounded(0I,0I)}}
                | _ -> operation) |> Map.add (id 5) (MemoryWitnessOperation.StringView view)
            let capacity={graph.CurrentClaims[id 32] with Body=ObligationBody.CapacityFits(32L,4096L)}
            {graph with
                Nodes=graph.Nodes.Add(id 43,node 43 (SemanticKind.PatternBinding "snapshot") (arrayOf uint8Type) [] None)
                                  .Add(id 32,node 32 (SemanticKind.Obligation capacity) unitType [] None)
                CurrentClaims=graph.CurrentClaims.Add(id 32,capacity)
                Obligations=graph.Obligations |> List.map(fun info->if info.Id=capacity.Id then capacity else info)
                Emission={graph.Emission with
                            Callable={graph.Emission.Callable with AliasTargets=graph.Emission.Callable.AliasTargets.Add(id 43,id 1)}
                            Numeric=
                                {graph.Emission.Numeric with
                                    Values=graph.Emission.Numeric.Values.Add(id 2,count)
                                    Elements=graph.Emission.Numeric.Elements.Add(id 1,byte)
                                    SourceTypes=graph.Emission.Numeric.SourceTypes.Add(id 43,arrayOf uint8Type)
                                    OccurrenceRepresentations=graph.Emission.Numeric.OccurrenceRepresentations.Add(id 43,Ok bytes)}
                            Memory={memory with Operations=operations;ArrayCopies=memory.ArrayCopies.Add(id 40,copy);Required=memory.Required.Add(id 1)}}}

        let private observeEmpty site graph =
            observe site graph (fun accumulator ->
                MLIRAccumulator.bindNode (id 43) (Arg 4) (TMemRef(TInt(IntWidth 8))) accumulator
                accumulator)

        let private changeEmpty change graph =
            let operations=graph.Emission.Memory.Operations |> Map.map(fun _ operation ->
                match operation with
                | MemoryWitnessOperation.EmptySnapshot row -> MemoryWitnessOperation.EmptySnapshot(change row)
                | MemoryWitnessOperation.Utf8Validation row ->
                    match row.Storage with
                    | MemoryCheckedSnapshotStorage.Empty empty -> MemoryWitnessOperation.Utf8Validation {row with Storage=MemoryCheckedSnapshotStorage.Empty(change empty)}
                    | _ -> operation
                | MemoryWitnessOperation.SnapshotRetirement row ->
                    match row.Storage with
                    | MemoryCheckedSnapshotStorage.Empty empty -> MemoryWitnessOperation.SnapshotRetirement {row with Storage=MemoryCheckedSnapshotStorage.Empty(change empty)}
                    | _ -> operation
                | _ -> operation)
            {graph with Emission={graph.Emission with Memory={graph.Emission.Memory with Operations=operations}}}

        [<Fact>]
        let ``empty returned snapshot emits one neutral actual producer value`` () =
            match observeEmpty 1 (emptyFixture ()) with
            | Ok(([EmptyBuffer(site,value) as operation],[],TRValue result),_) ->
                Assert.Equal(id 1,site)
                Assert.Equal(TMemRef(TInt(IntWidth 8)),value.Type)
                Assert.Equal(value,result)
                Assert.Equal(NeedsTargetRealization,moduleText (Ok 64) None [operation])
            | other -> failwithf "Empty producer lost its explicit neutral value: %A" other

        [<Theory>]
        [<InlineData(8)>]
        [<InlineData(13)>]
        let ``empty returned backing retirement discards without a free`` site =
            match observeEmpty site (emptyFixture ()) with
            | Ok(([],[],TRVoid),_) -> ()
            | other -> failwithf "Empty backing was allocated or freed: %A" other

        [<Theory>]
        [<InlineData("missing")>]
        [<InlineData("required")>]
        [<InlineData("owner")>]
        [<InlineData("type")>]
        [<InlineData("count")>]
        [<InlineData("declaration")>]
        let ``empty returned snapshot refuses missing or changed current evidence`` defect =
            let graph=emptyFixture ()
            let memory=graph.Emission.Memory
            let graph,reason =
                match defect with
                | "missing" -> {graph with Emission={graph.Emission with Memory={memory with Operations=memory.Operations.Remove(id 1)}}},"source-published contract"
                | "required" -> {graph with Emission={graph.Emission with Memory={memory with Required=memory.Required.Remove(id 1)}}},"source producer"
                | "owner" -> changeEmpty (fun row->{row with Owner=id 99}) graph,"source producer"
                | "type" -> changeEmpty (fun row->{row with SourceType=intType}) graph,"source producer"
                | "declaration" -> changeEmpty (fun row->{row with Declaration=id 99}) graph,"octet declaration"
                | _ ->
                    let values=graph.Emission.Numeric.Values
                    {graph with Emission={graph.Emission with Numeric={graph.Emission.Numeric with Values=values.Add(id 2,{values[id 2] with Range=ValueRange.Bounded(0I,1I)})}}},"zero-count copy"
            match observeEmpty 1 graph with
            | Result.Error actual -> Assert.Contains(reason,actual)
            | Ok _ -> failwithf "Empty snapshot %s evidence admitted" defect

        [<Fact>]
        let ``empty returned backing refuses an allocated retirement target`` () =
            let graph=emptyFixture ()
            let memory=graph.Emission.Memory
            let row=match memory.Operations[id 13] with MemoryWitnessOperation.CheckedResultRetirement row->row | _->failwith "fixture"
            let graph={graph with Emission={graph.Emission with Memory={memory with Operations=memory.Operations.Add(id 13,MemoryWitnessOperation.CheckedResultRetirement {row with Target=MemoryCheckedRetirementTarget.Backing})}}}
            match observeEmpty 13 graph with
            | Result.Error reason -> Assert.Contains("exact caller value or cleanup occurrence",reason)
            | Ok _ -> failwith "Empty backing acquired an allocated retirement"

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
