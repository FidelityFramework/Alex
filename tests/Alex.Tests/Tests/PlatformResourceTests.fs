module Alex.Tests.PlatformResourceTests

open Xunit
open Fidelity.PSG
open BAREWire.Descriptors
open Alex.Dialects.Core.Types
open Alex.Traversal.TransferTypes
open Alex.Tests.Build

module OwnedResourceRelease =
    let private id = NodeId

    let private handleType : TypeIdentity =
        TypeIdentity.Application(
            { Declaration = { Module = [ "Fixture" ]; Name = "Handle" }
              Parameters = []
              NativeKind = Some(NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Pointer)) },
            [])

    let private handleSlot = SettledSlot.CHandle(handleType, 64, 8)
    let private handleMlirType = TOpaqueHandle(handleType, 64, 8)

    let private resourceOptionRep =
        ValueRepresentation.Union(
            [ "None", []
              "Some", [ ValueRepresentation.Scalar handleSlot ] ],
            Some(0, 16, 8))

    let private resourceOptionType = optionOf handleType

    let private contract : BAREWire.Descriptors.ResourceDescriptor =
        { Resource =
            ResourceProtocol.OwnedNullableReturn
                { Binding = "Fixture.close"
                  Parameter = 0 }
          Hypothesis =
            { Identity = "fixture.resource"
              Version = "1"
              Source = "component contract" } }

    /// Positive configurations state the exact boundary contract rows that the
    /// compiler service publishes for owned resource calls and adaptations.
    /// Negative configurations isolate only the mismatched or withdrawn rows that
    /// PlatformPatterns.pBoundaryCall refuses.
    let private fixture (releaseResult: BoundaryScalar option) (callResult: BoundaryScalar option) (resultAdapt: Meet option) (includeMeet: bool) =
        let declarationId = id 10
        let acqBinding = id 11
        let acqBody = id 12
        let acqDesc = id 13
        let relBinding = id 14
        let relBody = id 15
        let relDesc = id 16
        let relFormal = id 17
        let acqSite = id 20
        let acqCallee = id 21
        let cleanupId = id 22
        let conversionId = id 23
        let handleActual = id 30
        let relSite = id 31
        let relCallee = id 32
        let support = Set.ofList [ declarationId; acqBinding; acqBody; acqDesc; relBinding; relBody; relDesc; relFormal; acqSite; acqCallee; cleanupId; conversionId; handleActual; relSite; relCallee ]

        let declaration : BoundaryResourceDeclaration =
            { Identity = declarationId
              Acquisition = acqBinding
              AcquisitionBody = acqBody
              AcquisitionDescriptor = acqDesc
              Release = relBinding
              ReleaseBody = relBody
              ReleaseDescriptor = relDesc
              ReleaseFormal = relFormal
              ReleaseOrdinal = 0
              PointerBits = 64
              AcquisitionType = unitType
              ResultType = resourceOptionType
              HandleType = handleType
              Contract = contract
              DeclarationFacts = Map.empty
              Participants = support }

        let acqImport : BoundaryImport =
            { Identity = acqDesc
              Binding = acqBinding
              Scope = acqBinding
              Library = "fixture"
              Symbol = "open"
              CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ acqBinding ]
              Parameters = []
              Result = Some(BoundaryScalar.ResourceHandle(declarationId, true))
              Participants = support
              SourceTypes = Map.empty
              DeclarationFacts = Map.empty }

        let relImport : BoundaryImport =
            { Identity = relDesc
              Binding = relBinding
              Scope = relBinding
              Library = "fixture"
              Symbol = "close"
              CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ relBinding ]
              Parameters = [ relFormal, BoundaryScalar.ResourceHandle(declarationId, false) ]
              Result = releaseResult
              Participants = support
              SourceTypes = Map.empty
              DeclarationFacts = Map.empty }

        let acqUse =
            BoundaryResourceUse.AcquireNullable
                { Declaration = declarationId
                  Tag = SettledSlot.Integer(8, None)
                  NoneCase = 0
                  SomeCase = 1
                  Conversion = conversionId
                  Cleanup = cleanupId }

        let acqCall : BoundaryCall =
            { Site = acqSite
              Import = acqDesc
              Callee = acqCallee
              Entry = None
              Arguments = []
              ErasedUnitArguments = []
              Result = Some(BoundaryScalar.ResourceHandle(declarationId, true))
              ResultAdaptation = None
              Resource = Some acqUse
              Participants = support
              SourceTypes = Map.empty }

        let relCall : BoundaryCall =
            { Site = relSite
              Import = relDesc
              Callee = relCallee
              Entry = None
              Arguments =
                [ { Actual = handleActual
                    Formal = relFormal
                    Abi = BoundaryScalar.ResourceHandle(declarationId, false)
                    Adaptation = None
                    OptionalEntry = None
                    BufferAbsence = None } ]
              ErasedUnitArguments = []
              Result = callResult
              ResultAdaptation = resultAdapt
              Resource =
                Some(
                    BoundaryResourceUse.ReleaseOwned
                        { Declaration = declarationId
                          Acquisition = acqSite
                          Cleanup = cleanupId })
              Participants = support
              SourceTypes = Map.empty }

        let relReturnType =
            match releaseResult with
            | Some _ -> intType
            | None -> unitType

        let nodes =
            [ node 21 (SemanticKind.PatternBinding "open") (functionFrom unitType resourceOptionType) [] None
              node 20 (SemanticKind.Application(acqCallee, [])) resourceOptionType [ 21 ] None
              node 30 (SemanticKind.PatternBinding "handle") handleType [] None
              node 32 (SemanticKind.PatternBinding "close") (functionFrom handleType relReturnType) [] None
              node 31 (SemanticKind.Application(relCallee, [ handleActual ])) relReturnType [ 32; 30 ] None ]

        let raw = revision nodes
        let meets =
            match resultAdapt with
            | Some meet when includeMeet -> Map.ofList [ relSite, [ meet ] ]
            | _ -> Map.empty

        { raw with
            Codata = { raw.Codata with Meets = meets }
            Emission =
                { raw.Emission with
                    Boundary =
                        { raw.Emission.Boundary with
                            Imports = Map.ofList [ acqDesc, acqImport; relDesc, relImport ]
                            Calls = Map.ofList [ acqSite, acqCall; relSite, relCall ]
                            ResourceDeclarations = Map.ofList [ declarationId, declaration ] }
                    Callable =
                        { raw.Emission.Callable with
                            AliasTargets = Map.ofList [ acqSite, acqSite; handleActual, handleActual; relSite, relSite ] }
                    Numeric =
                        { raw.Emission.Numeric with
                            OccurrenceRepresentations =
                                Map.ofList
                                    [ acqSite, Ok resourceOptionRep
                                      handleActual, Ok(ValueRepresentation.Scalar handleSlot) ] } } }
        |> declareTraversalReadings

    let private runAt site graph =
        let operands = MLIRAccumulator.empty ()
        MLIRAccumulator.bindNode (id 30) (SSA.Arg 0) handleMlirType operands
        let result = matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus graph graph.Nodes[site]) 64 operands
        Assert.Empty operands.AllOps
        Assert.True((MLIRAccumulator.recallNode site operands).IsNone)
        result

    [<Fact>]
    let ``ordinary option of the same handle type does not inherit resource ownership`` () =
        let graph = fixture None None None false
        let borrowed = id 40
        let representation =
            ValueRepresentation.Union(["None", []; "Some", [ValueRepresentation.Scalar handleSlot]], Some(8, 16, 8))
        let numeric =
            { graph.Emission.Numeric with
                OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations.Add(borrowed, Ok representation)
                TypeRepresentations = graph.Emission.Numeric.TypeRepresentations.Add(resourceOptionType, Ok representation) }
        let graph = { graph with Emission = { graph.Emission with Numeric = numeric } }
        Assert.False(Alex.CodeGeneration.TypeMapping.isResourceOccurrence graph borrowed)
        Assert.Equal(Ok(TMemRefStatic(16, TInt(IntWidth 8))), Alex.CodeGeneration.TypeMapping.valueTypeAt graph borrowed)
        Assert.Equal(Ok(TMemRefStatic(16, TInt(IntWidth 8))), Alex.CodeGeneration.TypeMapping.typeOfIdentity graph resourceOptionType)
        Assert.True(Alex.CodeGeneration.TypeMapping.isResourceOccurrence graph (id 20))
        Assert.Equal(Ok(TResourceOption resourceOptionRep), Alex.CodeGeneration.TypeMapping.valueTypeAt graph (id 20))

    [<Fact>]
    let ``ordinary nullable handle refuses an absent published layout`` () =
        let missing = ValueRepresentation.Union(["None", []; "Some", [ValueRepresentation.Scalar handleSlot]], None)
        match Alex.CodeGeneration.TypeMapping.ordinaryRepresentationType missing with
        | Result.Error reason -> Assert.Contains("complete source-settled", reason)
        | Ok _ -> failwith "Nullable handle acquired storage without layout."

    [<Fact>]
    let ``void ReleaseOwned produces void ResourceCall with None result`` () =
        let graph = fixture None None None false
        match runAt (id 31) graph with
        | Result.Ok(([ MLIROp.ResourceCall(site, [ actual ], None) ], TRVoid), _) ->
            Assert.Equal(id 31, site)
            Assert.Equal({ SSA = SSA.Arg 0; Type = handleMlirType }, actual)
        | other -> failwithf "Unexpected void ReleaseOwned witness: %A" other

    [<Fact>]
    let ``signed 32-bit ReleaseOwned without adaptation returns i32 ResourceCall result`` () =
        let status = Some(BoundaryScalar.Integer(32, true))
        let graph = fixture status status None false
        match runAt (id 31) graph with
        | Result.Ok(([ MLIROp.ResourceCall(site, [ actual ], Some raw) ], TRValue result), _) ->
            Assert.Equal(id 31, site)
            Assert.Equal({ SSA = SSA.Arg 0; Type = handleMlirType }, actual)
            Assert.Equal(TInt(IntWidth 32), raw.Type)
            Assert.Equal(raw, result)
        | other -> failwithf "Unexpected unadapted int32 ReleaseOwned witness: %A" other

    [<Fact>]
    let ``signed 32-bit ReleaseOwned with published widening adaptation emits ExtSI`` () =
        let status = Some(BoundaryScalar.Integer(32, true))
        let meet = { Consumer = id 31; Operand = id 31; From = 32; To = 64; Adapt = MeetKind.ExtendSigned }
        let graph = fixture status status (Some meet) true
        match runAt (id 31) graph with
        | Result.Ok(([ MLIROp.ResourceCall(site, [ actual ], Some raw);
                       MLIROp.ArithOp(ArithOp.ExtSI(adapted, source, fromTy, toTy)) ], TRValue result), _) ->
            Assert.Equal(id 31, site)
            Assert.Equal({ SSA = SSA.Arg 0; Type = handleMlirType }, actual)
            Assert.Equal(TInt(IntWidth 32), raw.Type)
            Assert.Equal(raw.SSA, source)
            Assert.NotEqual(raw.SSA, adapted)
            Assert.Equal(TInt(IntWidth 32), fromTy)
            Assert.Equal(TInt(IntWidth 64), toTy)
            Assert.Equal({ SSA = adapted; Type = TInt(IntWidth 64) }, result)
        | other -> failwithf "Unexpected adapted int32 ReleaseOwned witness: %A" other

    [<Fact>]
    let ``void ReleaseOwned refuses numeric result adaptation`` () =
        let meet = { Consumer = id 31; Operand = id 31; From = 32; To = 64; Adapt = MeetKind.ExtendSigned }
        let graph = fixture None None (Some meet) true
        match runAt (id 31) graph with
        | Result.Error reason ->
            Assert.Equal("Owned resource release differs from its exact unary void or signed 32-bit status declaration.", reason)
        | Result.Ok other -> failwithf "Void ReleaseOwned admitted result adaptation: %A" other

    [<Theory>]
    [<InlineData(64, true)>]
    [<InlineData(32, false)>]
    let ``ReleaseOwned refuses integer status width or signedness other than signed 32-bit`` bits isSigned =
        let status = Some(BoundaryScalar.Integer(bits, isSigned))
        let graph = fixture status status None false
        match runAt (id 31) graph with
        | Result.Error reason ->
            Assert.Equal("Owned resource release differs from its exact unary void or signed 32-bit status declaration.", reason)
        | Result.Ok other -> failwithf "ReleaseOwned admitted non-int32 status (%d, %b): %A" bits isSigned other

    [<Fact>]
    let ``ReleaseOwned refuses import vs call result mismatch`` () =
        let status = Some(BoundaryScalar.Integer(32, true))
        let graph = fixture status None None false
        match runAt (id 31) graph with
        | Result.Error reason ->
            Assert.Equal("Owned resource release differs from its exact unary void or signed 32-bit status declaration.", reason)
        | Result.Ok other -> failwithf "ReleaseOwned admitted import/call result mismatch: %A" other

    [<Fact>]
    let ``signed 32-bit ReleaseOwned refuses withdrawn source numeric meet`` () =
        let status = Some(BoundaryScalar.Integer(32, true))
        let meet = { Consumer = id 31; Operand = id 31; From = 32; To = 64; Adapt = MeetKind.ExtendSigned }
        let graph = fixture status status (Some meet) false
        match runAt (id 31) graph with
        | Result.Error reason -> Assert.Equal("Published adaptation disagrees with its exact source numeric meet.", reason)
        | Result.Ok other -> failwithf "ReleaseOwned admitted withdrawn meet: %A" other

    [<Fact>]
    let ``AcquireNullable still refuses numeric result adaptation`` () =
        let baseGraph = fixture None None None false
        let meet = { Consumer = id 20; Operand = id 20; From = 32; To = 64; Adapt = MeetKind.ExtendSigned }
        let acqCall = { baseGraph.Emission.Boundary.Calls[id 20] with ResultAdaptation = Some meet }
        let graph =
            { baseGraph with
                Codata = { baseGraph.Codata with Meets = Map.ofList [ id 20, [ meet ] ] }
                Emission =
                    { baseGraph.Emission with
                        Boundary = { baseGraph.Emission.Boundary with Calls = baseGraph.Emission.Boundary.Calls.Add(id 20, acqCall) } } }
        match runAt (id 20) graph with
        | Result.Error reason -> Assert.Equal("Resource conversion cannot be replaced by a numeric result adaptation.", reason)
        | Result.Ok other -> failwithf "AcquireNullable admitted result adaptation: %A" other

/// Reduced explicit pattern-level fixtures under AGENTS.md fixture rules: each
/// case states the exact published Boundary/Callable/Numeric/Obligation rows
/// read by the Pattern or Transfer under test while isolating positive
/// witnessing and negative refusals.
module Schema53BoundaryWitnessing =
    let private id = NodeId

    let private emptyFact (form: string) : BoundaryDeclarationFact =
        { Form = form; SourceType = unitType; Text = []; Numbers = []; References = []; Children = []; Parent = None }

    let private ptrHandleType : TypeIdentity =
        TypeIdentity.Application(
            { Declaration = { Module = [ "Fidelity"; "Platform"; "Native" ]; Name = "CHandle" }
              Parameters = [ TypeParamKind.Type ]
              NativeKind = Some NTUKind.NTUptr },
            [ unitType ])

    let private handleRep = ValueRepresentation.Scalar(SettledSlot.CHandle(ptrHandleType, 64, 8))
    let private bufRep = ValueRepresentation.Buffer(None, ValueRepresentation.Scalar(SettledSlot.Integer(8, Some "uint8")))
    let private optBufRep =
        ValueRepresentation.Union(
            [ "None", []
              "Some", [ bufRep ] ],
            Some(0, 24, 8))

    let private fixedDescriptorFacts (descId: NodeId) (arrId: NodeId) (fixedP: NodeId) (p1: NodeId) (p2Opt: NodeId option) =
        let fixedCase = id 950
        let fixedPassBy = { emptyFact "case" with Text = [ "Fixed" ] }
        let normalPassBy = id 951
        let normalCase = { emptyFact "case" with Text = [ "Value" ] }
        let fixedRec =
            { emptyFact "record" with
                Text = [ "PassBy" ]
                References = [ fixedCase ]
                Children = [ fixedCase ] }
        let normalRec =
            { emptyFact "record" with
                Text = [ "PassBy" ]
                References = [ normalPassBy ]
                Children = [ normalPassBy ] }
        let pRefs =
            match p2Opt with
            | Some p2 -> [ fixedP; p1; p2 ]
            | None -> [ fixedP; p1 ]
        let arrFact = { emptyFact "array" with References = pRefs; Children = pRefs }
        let descFact =
            { emptyFact "record" with
                Text = [ "Parameters" ]
                References = [ arrId ]
                Children = [ arrId ] }
        let baseFacts =
            Map.ofList
                [ fixedCase, fixedPassBy
                  normalPassBy, normalCase
                  fixedP, fixedRec
                  p1, normalRec
                  arrId, arrFact
                  descId, descFact ]
        match p2Opt with
        | Some p2 -> baseFacts.Add(p2, normalRec)
        | None -> baseFacts

    let private mkNode (NodeId n) (ty: TypeIdentity) (kind: SemanticKind) (children: NodeId list) =
        node n kind ty (List.map NodeId.value children) None

    let private runBoundaryCallAt (siteId: NodeId) (graph: Revision) =
        let g = declareTraversalReadings graph
        let acc = MLIRAccumulator.empty ()
        for (nid, repRes) in Map.toList g.Emission.Numeric.OccurrenceRepresentations do
            match repRes with
            | Result.Ok rep when nid <> siteId ->
                let ssa =
                    match nid with
                    | NodeId 0 -> Arg 0
                    | NodeId 1 -> Arg 1
                    | NodeId k -> V(k, 0)
                MLIRAccumulator.bindNode nid ssa (Alex.CodeGeneration.TypeMapping.representationType rep |> Result.defaultWith failwith) acc
            | _ -> ()
        let result = matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus g g.Nodes[siteId]) 64 acc
        Assert.Empty acc.AllOps
        Assert.True((MLIRAccumulator.recallNode siteId acc).IsNone)
        result

    let private obligation (oid: NodeId) (kind: string) (body: ObligationBody) : ObligationInfo =
        { Id = sprintf "ob_%d" (NodeId.value oid)
          Kind = kind
          Logic = "QF_LIA"
          Statement = "fixture obligation"
          Source = "Fixture.clef:1:1"
          Refs = [ "fixture"; "1"; "component contract" ]
          Body = body }

    /// Publishes an ExplicitZeroCopy fixture with a leading PassBy.Fixed sentinel
    /// at native ordinal 0 (buffer at native ordinal 1 -> call.Arguments[0],
    /// count at native ordinal 2 -> call.Arguments[1]).
    let private explicitZeroCopyFixture (retentionOk: bool) (extentValid: bool) =
        let roId = id 50
        let declBinding = id 51
        let bodyId = id 52
        let descId = id 53
        let fixedParam = id 952
        let bufFormal = id 54
        let countFormal = id 55
        let siteId = id 60
        let calleeId = id 61
        let bufActual = id 0
        let countActual = id 1
        let resId = id 62
        let extentClaimId = id 63
        let retentionClaimId = id 64
        let support = Set.ofList [ roId; declBinding; bodyId; descId; fixedParam; bufFormal; countFormal; siteId; calleeId; bufActual; countActual; resId; extentClaimId; retentionClaimId ]
        let descFacts = fixedDescriptorFacts descId (id 953) fixedParam bufFormal (Some countFormal)
        let roDecl : BoundaryReadOnlyBufferDeclaration =
            { Identity = roId; Declaration = declBinding; Body = bodyId
              Formals = [ bufFormal; countFormal ]; Descriptor = descId
              Parameter = 1; CountParameter = Some 2; BufferFormal = bufFormal; CountFormal = Some countFormal
              Contract =
                { Binding = "Fixture.writeBytes"; Parameter = 1
                  Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.ExplicitCount 2
                  Content = BAREWire.Descriptors.BorrowedContent.RawBytes
                  Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                  Hypothesis = { Identity = "fixture.ro"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let roUse : BoundaryReadOnlyBufferUse =
            { Call = siteId; Declaration = roId; Parameter = 1; Buffer = bufActual; Residence = resId
              Retirements = []; Copies = 0
              Crossing = BoundaryReadOnlyBufferCrossing.ExplicitZeroCopy(2, countActual, 16I, extentClaimId)
              RetentionProof = retentionClaimId; AccessExclusivityProof = None
              Participants = ParticipantEvidence.Established [] }
        let extentOb =
            obligation extentClaimId "foreign-readonly-buffer-extent"
                (ObligationBody.ZeroCopyBufferExtent
                    { Call = siteId; Declaration = roId; Parameter = 1; CountParameter = 2
                      Buffer = bufActual; Count = countActual; MinimumCount = 1I
                      MaximumCount = 8I
                      ExtentCapacity = if extentValid then 16I else 32I
                      ElementBytes = 1; CountCoverage = extentClaimId })
        let retentionOb =
            obligation retentionClaimId "foreign-buffer-retention-domination"
                (ObligationBody.BufferRetentionDomination
                    { Call = siteId; Declaration = roId
                      Buffer = if retentionOk then bufActual else id 999
                      Residence = resId
                      Mode = BufferRetentionMode.DuringCall
                      AcquireOrder = 1
                      RetirementOrders = [] })
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding
              Library = "fixture"; Symbol = "fixture_write_bytes"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]
              Parameters = [ bufFormal, BoundaryScalar.ReadOnlyBytes roId; countFormal, BoundaryScalar.Integer(32, true) ]
              Result = Some(BoundaryScalar.Integer(32, true))
              Participants = support; SourceTypes = Map.empty; DeclarationFacts = descFacts }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments =
                [ { Actual = bufActual; Formal = bufFormal; Abi = BoundaryScalar.ReadOnlyBytes roId; Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = countActual; Formal = countFormal; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.Integer(32, true)); ResultAdaptation = None
              Participants = support; SourceTypes = Map.empty }
        let nodes =
            Map.ofList
                [ siteId, mkNode siteId intType (SemanticKind.Application(calleeId, [ bufActual; countActual ])) [ calleeId; bufActual; countActual ]
                  calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_write_bytes", Some declBinding)) []
                  bufActual, mkNode bufActual unitType (SemanticKind.VarRef("buf", None)) []
                  countActual, mkNode countActual intType (SemanticKind.PatternBinding "n") []
                  extentClaimId, mkNode extentClaimId unitType (SemanticKind.Obligation extentOb) []
                  retentionClaimId, mkNode retentionClaimId unitType (SemanticKind.Obligation retentionOb) [] ]
        let emptyGraph = revision []
        let baseBoundary = emptyGraph.Emission.Boundary
        let baseNumeric = emptyGraph.Emission.Numeric
        { emptyGraph with
            Nodes = nodes
            Obligations = [ extentOb; retentionOb ]
            Emission =
                { emptyGraph.Emission with
                    Callable = { emptyGraph.Emission.Callable with AliasTargets = Map.ofList [ siteId, siteId ] }
                    Numeric =
                        { baseNumeric with
                            Values =
                                Map.ofList
                                    [ countActual,
                                      { Site = countActual
                                        Slot = SettledSlot.Integer(32, Some "int32")
                                        Range = ValueRange.Bounded(1I, 8I)
                                        Representation = None
                                        Declaration = None
                                        SourceType = intType
                                        Obligations = []
                                        Participants = Set.singleton countActual } ]
                            OccurrenceRepresentations =
                                Map.ofList
                                    [ bufActual, Result.Ok bufRep
                                      countActual, Result.Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32"))) ] }
                    Boundary =
                        { baseBoundary with
                            Imports = Map.ofList [ descId, importRow ]
                            Calls = Map.ofList [ siteId, callRow ]
                            ReadOnlyBufferDeclarations = Map.ofList [ roId, roDecl ]
                            ReadOnlyBufferUses = Map.ofList [ (siteId, 1), roUse ] } } }

    [<Fact>]
    let ``ExplicitZeroCopy with leading PassBy Fixed sentinel emits deferred BoundaryBufferCall`` () =
        let graph = explicitZeroCopyFixture true true
        match runBoundaryCallAt (id 60) graph with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 60, [ { Type = TMemRef(TInt(IntWidth 8)) }; { Type = TInt(IntWidth 32) } ], [], [], [ { Type = TInt(IntWidth 32) } ]) ] as ops, TRValue _), _) ->
            let scopedBoundary = { graph.Emission.Boundary with ByScope = Map.ofList [ id 51, [ id 53 ] ] }
            match Alex.Patterns.PlatformPatterns.boundaryImportsAt (id 51) scopedBoundary with
            | Result.Ok [ MLIROp.FuncOp(FuncOp.BoundaryFuncDecl(imp, [ TMemRef(TInt(IntWidth 8)); TInt(IntWidth 32) ], [ TInt(IntWidth 32) ])) as decl ] ->
                Assert.Equal(id 53, imp.Identity)
                Assert.Equal(Result.Ok NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [ decl ])
                Assert.Equal(Result.Ok NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None ops)
            | other -> failwithf "Unexpected boundaryImportsAt result for ExplicitZeroCopy: %A" other
        | other -> failwithf "Unexpected ExplicitZeroCopy result: %A" other

    [<Fact>]
    let ``ExplicitZeroCopy refuses withdrawn extent coverage and invalid retention domination`` () =
        match runBoundaryCallAt (id 60) (explicitZeroCopyFixture true false) with
        | Result.Error reason ->
            Assert.Equal("Read-only buffer argument at boundary call 60 operand 0 lacks its exact source crossing, extent/termination, or retention account.", reason)
        | Result.Ok other -> failwithf "Admitted invalid ExplicitZeroCopy extent coverage: %A" other
        match runBoundaryCallAt (id 60) (explicitZeroCopyFixture false true) with
        | Result.Error reason ->
            Assert.Equal("Read-only buffer argument at boundary call 60 operand 0 lacks its exact source crossing, extent/termination, or retention account.", reason)
        | Result.Ok other -> failwithf "Admitted invalid BufferRetentionDomination: %A" other
        let validGraph = explicitZeroCopyFixture true true
        let wrongCountNodeGraph =
            let badExtentOb =
                obligation (id 63) "foreign-readonly-buffer-extent"
                    (ObligationBody.ZeroCopyBufferExtent
                        { Call = id 60; Declaration = id 50; Parameter = 1; CountParameter = 2
                          Buffer = id 0; Count = id 999; MinimumCount = 1I
                          MaximumCount = 8I; ExtentCapacity = 16I; ElementBytes = 1; CountCoverage = id 63 })
            { validGraph with
                Nodes = Map.add (id 63) (mkNode (id 63) unitType (SemanticKind.Obligation badExtentOb) []) validGraph.Nodes
                Obligations =
                    validGraph.Obligations
                    |> List.map (fun ob -> if ob.Kind = "foreign-readonly-buffer-extent" then badExtentOb else ob) }
        match runBoundaryCallAt (id 60) wrongCountNodeGraph with
        | Result.Error reason ->
            Assert.Equal("Read-only buffer argument at boundary call 60 operand 0 lacks its exact source crossing, extent/termination, or retention account.", reason)
        | Result.Ok other -> failwithf "Admitted ExplicitZeroCopy with mismatched ZeroCopyBufferExtent count node: %A" other
        let wrongCountArgGraph =
            let origCall = validGraph.Emission.Boundary.Calls[id 60]
            let badArgs = origCall.Arguments |> List.mapi (fun idx a -> if idx = 1 then { a with Actual = id 999 } else a)
            { validGraph with
                Emission =
                    { validGraph.Emission with
                        Boundary =
                            { validGraph.Emission.Boundary with
                                Calls = Map.add (id 60) { origCall with Arguments = badArgs } validGraph.Emission.Boundary.Calls } } }
        match runBoundaryCallAt (id 60) wrongCountArgGraph with
        | Result.Error reason ->
            Assert.Equal("Read-only buffer argument at boundary call 60 operand 0 lacks its exact source crossing, extent/termination, or retention account.", reason)
        | Result.Ok other -> failwithf "Admitted ExplicitZeroCopy with mismatched call count actual: %A" other

    [<Theory>]
    [<InlineData("static-ok", true, true)>]
    [<InlineData("static-missing-origin", false, true)>]
    [<InlineData("staged-ok", true, false)>]
    [<InlineData("staged-mismatched-claim", false, false)>]
    let ``uncounted NUL paths admit valid static/staged crossings and refuse defective ones`` _ shouldPass isStatic =
        let roId = id 150
        let declBinding = id 151
        let bodyId = id 152
        let descId = id 153
        let bufFormal = id 154
        let siteId = id 160
        let calleeId = id 161
        let bufActual = id 0
        let resId = id 162
        let termClaimId = id 163
        let retClaimId = id 164
        let stagedBufId = id 165
        let support = Set.ofList [ roId; declBinding; bodyId; descId; bufFormal; siteId; calleeId; bufActual; resId; termClaimId; retClaimId; stagedBufId ]
        let descFacts =
            let pCase = id 960
            let pRec = { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
            let arrId = id 961
            Map.ofList
                [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                  bufFormal, pRec
                  arrId, { emptyFact "array" with References = [ bufFormal ]; Children = [ bufFormal ] }
                  descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let roDecl : BoundaryReadOnlyBufferDeclaration =
            { Identity = roId; Declaration = declBinding; Body = bodyId
              Formals = [ bufFormal ]; Descriptor = descId
              Parameter = 0; CountParameter = None; BufferFormal = bufFormal; CountFormal = None
              Contract =
                { Binding = "Fixture.puts"; Parameter = 0
                  Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                  Hypothesis = { Identity = "fixture.uncounted"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let crossing =
            if isStatic then BoundaryReadOnlyBufferCrossing.StaticImageNulBorrowed(0, bufActual, 2I, termClaimId)
            else
                let cap = if shouldPass then 3 else 2
                BoundaryReadOnlyBufferCrossing.CallScopedNulStaged(stagedBufId, cap, 2I, termClaimId)
        let roUse : BoundaryReadOnlyBufferUse =
            { Call = siteId; Declaration = roId; Parameter = 0; Buffer = bufActual; Residence = resId
              Retirements = []; Copies = 0; Crossing = crossing; RetentionProof = retClaimId; AccessExclusivityProof = None
              Participants = ParticipantEvidence.Established [] }
        let termMode =
            if isStatic then UncountedPathStagingMode.StaticImageZeroCopy 0
            else UncountedPathStagingMode.CallScopedStaged(stagedBufId, 3)
        let termOb =
            obligation termClaimId "foreign-uncounted-path-termination"
                (ObligationBody.UncountedPathTermination
                    { Call = siteId; Declaration = roId; Parameter = 0; Source = bufActual; ByteLength = 2I
                      Mode = termMode; RequiresNoInteriorNul = true; RequiresTrailingNul = true })
        let retOb =
            obligation retClaimId "foreign-buffer-retention-domination"
                (ObligationBody.BufferRetentionDomination
                    { Call = siteId; Declaration = roId; Buffer = bufActual; Residence = resId
                      Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
        let pool : StaticStringPool option =
            if not isStatic then None
            else
                Some
                    { Symbol = ".rodata.str"; Bytes = [ 104uy; 105uy; 0uy ]; Alignment = 1; Size = 3; UsedSize = 3
                      Entries = [ { Content = "hi"; Offset = 0; Length = 2; StorageLength = 3; NodeIds = (if shouldPass then [ bufActual ] else []) } ]
                      SpaceName = "rodata"; Capacity = 16L; SpaceAlignment = 1; Granularity = 1; DeclarationNode = declBinding }
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding
              Library = "fixture"; Symbol = "fixture_puts"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]; Parameters = [ bufFormal, BoundaryScalar.ReadOnlyBytes roId ]
              Result = None; Participants = support; SourceTypes = Map.empty; DeclarationFacts = descFacts }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments = [ { Actual = bufActual; Formal = bufFormal; Abi = BoundaryScalar.ReadOnlyBytes roId; Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = None; ResultAdaptation = None; Participants = support; SourceTypes = Map.empty }
        let emptyGraph = revision []
        let graph =
            { emptyGraph with
                StaticStringPool = pool
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ bufActual ])) [ calleeId; bufActual ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_puts", Some declBinding)) []
                          bufActual, mkNode bufActual unitType (SemanticKind.VarRef("s", None)) []
                          termClaimId, mkNode termClaimId unitType (SemanticKind.Obligation termOb) []
                          retClaimId, mkNode retClaimId unitType (SemanticKind.Obligation retOb) [] ]
                Obligations = [ termOb; retOb ]
                Emission =
                    { emptyGraph.Emission with
                        Numeric = { emptyGraph.Emission.Numeric with OccurrenceRepresentations = Map.ofList [ bufActual, Result.Ok bufRep ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow ]
                                Calls = Map.ofList [ siteId, callRow ]
                                ReadOnlyBufferDeclarations = Map.ofList [ roId, roDecl ]
                                ReadOnlyBufferUses = Map.ofList [ (siteId, 0), roUse ] } } }
        match runBoundaryCallAt siteId graph, shouldPass with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 160, [ { Type = TMemRef(TInt(IntWidth 8)) } ], [], [], []) ], TRVoid), _), true -> ()
        | Result.Error reason, false ->
            Assert.Equal("Read-only buffer argument at boundary call 160 operand 0 lacks its exact source crossing, extent/termination, or retention account.", reason)
        | other, expected -> failwithf "Unexpected uncounted NUL result (expected=%b): %A" expected other

    /// Direct and conditional BufferAbsence conversions witness option slots without
    /// introducing nullable memrefs or mutating the original argument vector, including
    /// when a leading PassBy.Fixed parameter shifts native ordinal vs call argument index.
    [<Theory>]
    [<InlineData("direct-none", true, false, false)>]
    [<InlineData("direct-some", true, true, false)>]
    [<InlineData("direct-fixed-some", true, true, true)>]
    [<InlineData("direct-missing-claim", false, false, false)>]
    [<InlineData("cond-ok", true, true, false)>]
    [<InlineData("cond-reversed-ok", true, false, false)>]
    [<InlineData("cond-missing-select", false, true, false)>]
    let ``BufferAbsence Direct and Conditional conversions witness BoundaryBufferCall slots and refuse gaps`` (mode: string) shouldPass flag leadingFixed =
        let roId = id 250
        let declBinding = id 251
        let bodyId = id 252
        let descId = id 253
        let fixedParam = id 972
        let bufFormal = id 254
        let siteId = id 260
        let calleeId = id 261
        let optActual = id 0
        let payloadId = id 262
        let quoteId = id 263
        let absClaimPresent = id 264
        let absClaimAbsent = id 265
        let resId = id 266
        let termClaimId = id 267
        let retClaimId = id 268
        let stagedBufId = id 269
        let tagProjId = id 270
        let otherConstruct = id 271
        let nativeParam = if leadingFixed then 1 else 0
        let support = Set.ofList [ roId; declBinding; bodyId; descId; bufFormal; siteId; calleeId; optActual; payloadId; quoteId; absClaimPresent; absClaimAbsent; resId; termClaimId; retClaimId; stagedBufId; tagProjId ]
        let descFacts =
            if leadingFixed then
                fixedDescriptorFacts descId (id 971) fixedParam bufFormal None
            else
                let pCase = id 970
                let arrId = id 971
                Map.ofList
                    [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                      bufFormal, { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
                      arrId, { emptyFact "array" with References = [ bufFormal ]; Children = [ bufFormal ] }
                      descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let roDecl : BoundaryReadOnlyBufferDeclaration =
            { Identity = roId; Declaration = declBinding; Body = bodyId; Formals = [ bufFormal ]; Descriptor = descId
              Parameter = nativeParam; CountParameter = None; BufferFormal = bufFormal; CountFormal = None
              Contract =
                { Binding = "Fixture.openVfs"; Parameter = nativeParam
                  Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                  Hypothesis = { Identity = "fixture.vfs.ro"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let absContract : BAREWire.Descriptors.BufferAbsenceContract =
            { Binding = "Fixture.openVfs"; Parameter = nativeParam
              Hypothesis = { Identity = "fixture.vfs.abs"; Version = "1"; Source = "component contract" } }
        let absRow : BoundaryBufferAbsence =
            { Quote = quoteId; DescriptorBinding = id 272; Record = id 273; Import = descId; Parameter = nativeParam; Formal = bufFormal
              BufferDeclaration = roId; Contract = absContract; SourcePath = []; Inputs = []; DeclarationFacts = Map.empty }
        let arms =
            [ { BufferAbsencePlanArm.CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
              { BufferAbsencePlanArm.CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer } ]
        let mkAbsOb (oid: NodeId) (construction: NodeId) (srcCase: int) =
            obligation oid "foreign-buffer-absence-conversion-0"
                (ObligationBody.BufferAbsenceArgumentConversion
                    { Call = siteId; Parameter = 0; Actual = optActual; Construction = construction
                      SourceCase = srcCase; Absence = quoteId; Arms = arms })
        let absObAbsent = mkAbsOb absClaimAbsent (if mode.StartsWith "cond" then otherConstruct else optActual) 0
        let absObPresent = mkAbsOb absClaimPresent optActual 1
        let roUse : BoundaryReadOnlyBufferUse =
            { Call = siteId; Declaration = roId; Parameter = nativeParam; Buffer = optActual; Residence = resId
              Retirements = []; Copies = 0
              Crossing = BoundaryReadOnlyBufferCrossing.CallScopedNulStaged(stagedBufId, 3, 2I, termClaimId)
              RetentionProof = retClaimId; AccessExclusivityProof = None; Participants = ParticipantEvidence.Established [] }
        let termOb =
            obligation termClaimId "foreign-uncounted-path-termination"
                (ObligationBody.UncountedPathTermination
                    { Call = siteId; Declaration = roId; Parameter = nativeParam; Source = optActual; ByteLength = 2I
                      Mode = UncountedPathStagingMode.CallScopedStaged(stagedBufId, 3)
                      RequiresNoInteriorNul = true; RequiresTrailingNul = true })
        let retOb =
            obligation retClaimId "foreign-buffer-retention-domination"
                (ObligationBody.BufferRetentionDomination
                    { Call = siteId; Declaration = roId; Buffer = optActual; Residence = resId
                      Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
        let presentSel : BoundaryBufferAbsenceSelection =
            { Construction = optActual; CaseOrdinal = 1; Payload = Some payloadId; Absence = quoteId; Transport = [ optActual ]; Obligation = absClaimPresent }
        let absentSel : BoundaryBufferAbsenceSelection =
            { Construction = (if mode.StartsWith "cond" then otherConstruct else optActual); CaseOrdinal = 0; Payload = None; Absence = quoteId; Transport = [ optActual; otherConstruct ]; Obligation = absClaimAbsent }
        let choice =
            match mode with
            | "direct-none" | "direct-missing-claim" -> BoundaryBufferAbsenceChoice.Direct absentSel
            | "direct-some" | "direct-fixed-some" -> BoundaryBufferAbsenceChoice.Direct presentSel
            | _ ->
                let wT, wF = if flag then presentSel, absentSel else absentSel, presentSel
                BoundaryBufferAbsenceChoice.Conditional(optActual, tagProjId, wT, wF)
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding; Library = "fixture"; Symbol = "fixture_open_vfs"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]; Parameters = [ bufFormal, BoundaryScalar.ReadOnlyBytes roId ]; Result = None
              Participants = support; SourceTypes = Map.empty; DeclarationFacts = descFacts }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments = [ { Actual = optActual; Formal = bufFormal; Abi = BoundaryScalar.ReadOnlyBytes roId; Adaptation = None; OptionalEntry = None; BufferAbsence = Some choice } ]
              ErasedUnitArguments = []; Result = None; ResultAdaptation = None; Participants = support; SourceTypes = Map.empty }
        let tagCarrier : ScalarCarrier =
            { Site = tagProjId; Slot = SettledSlot.Integer(8, Some "uint8"); Range = ValueRange.Bounded(0I, 1I)
              Representation = None; Declaration = None; SourceType = uint8Type; Obligations = []
              Participants = Set.singleton optActual }
        let selectRow : CallableAggregateValue =
            { Occurrence = optActual; Aggregate = optActual; Slot = id 0
              Alternatives = []; Selector = None; FormationInputs = []; Value = None; SelectedAlternative = None
              Operation = CallableAggregateOperation.Select; ResultRetirement = None; Frontier = None; Tag = None
              Selection = Some { Condition = tagProjId; WhenTrue = (if flag then optActual else otherConstruct); WhenFalse = (if flag then otherConstruct else optActual) }
              Bytes = 0; Alignment = 1; Participants = [] }
        let baseNodes =
            Map.ofList
                [ siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ optActual ])) [ calleeId; optActual; tagProjId ]
                  calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_open_vfs", Some declBinding)) []
                  optActual, mkNode optActual unitType (SemanticKind.VarRef("vfsOpt", None)) []
                  tagProjId, { mkNode tagProjId uint8Type (SemanticKind.DUGetTag(optActual, unitType)) [ optActual ] with ValueRange = Some(ValueRange.Bounded(0I, 1I)) }
                  termClaimId, mkNode termClaimId unitType (SemanticKind.Obligation termOb) []
                  retClaimId, mkNode retClaimId unitType (SemanticKind.Obligation retOb) [] ]
        let allNodes =
            if mode = "direct-missing-claim" then baseNodes
            else
                baseNodes
                    .Add(absClaimAbsent, mkNode absClaimAbsent unitType (SemanticKind.Obligation absObAbsent) [])
                    .Add(absClaimPresent, mkNode absClaimPresent unitType (SemanticKind.Obligation absObPresent) [])
        let emptyGraph = revision []
        let graph =
            { emptyGraph with
                Nodes = allNodes
                Obligations = [ absObAbsent; absObPresent; termOb; retOb ]
                Emission =
                    { emptyGraph.Emission with
                        Callable =
                            { emptyGraph.Emission.Callable with
                                AggregateValues =
                                    if mode = "cond-missing-select" then Map.empty
                                    else Map.ofList [ optActual, [ selectRow ] ] }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                Values = Map.ofList [ tagProjId, tagCarrier ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ optActual, Result.Ok optBufRep
                                          payloadId, Result.Ok bufRep
                                          tagProjId, Result.Ok(ValueRepresentation.Scalar(SettledSlot.Integer(8, Some "uint8"))) ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow ]
                                Calls = Map.ofList [ siteId, callRow ]
                                ReadOnlyBufferDeclarations = Map.ofList [ roId, roDecl ]
                                ReadOnlyBufferUses = Map.ofList [ (siteId, nativeParam), roUse ]
                                BufferAbsences = Map.ofList [ quoteId, absRow ] } } }
        match runBoundaryCallAt siteId graph, shouldPass with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 260, [ { SSA = Arg 0 } ], [], [ { BufferOrdinal = 0; Plan = plan } ], []) ], TRVoid), _), true ->
            match mode, plan with
            | "direct-none", BufferAbsenceSlotChoice.Direct { CaseOrdinal = 0; Buffer = None } -> ()
            | ("direct-some" | "direct-fixed-some"), BufferAbsenceSlotChoice.Direct { CaseOrdinal = 1; Buffer = Some { Type = TMemRef(TInt(IntWidth 8)) } } -> ()
            | "cond-ok", BufferAbsenceSlotChoice.Conditional(_, _, { CaseOrdinal = 1; Buffer = Some _ }, { CaseOrdinal = 0; Buffer = None }) -> ()
            | "cond-reversed-ok", BufferAbsenceSlotChoice.Conditional(_, _, { CaseOrdinal = 0; Buffer = None }, { CaseOrdinal = 1; Buffer = Some _ }) -> ()
            | other -> failwithf "Unexpected BufferAbsence slot plan %A for mode %s" other mode
        | Result.Error reason, false ->
            if mode = "direct-missing-claim" then
                Assert.Equal("Optional byte-buffer absence conversion at boundary call 260 operand 0 lacks its exact BufferAbsenceContract or claim.", reason)
            else
                Assert.Equal("Conditional byte-buffer absence conversion at boundary call 260 operand 0 requires source-authored assigned tag projection and both arm accounts.", reason)
        | other, expected -> failwithf "Unexpected BufferAbsence result (mode=%s expected=%b): %A" mode expected other
        if mode = "direct-none" then
            let indirectAbsGraph =
                { graph with
                    Emission =
                        { graph.Emission with
                            Boundary =
                                { graph.Emission.Boundary with
                                    Calls = Map.ofList [ siteId, { callRow with Entry = Some(id 275) } ] } } }
            match runBoundaryCallAt siteId indirectAbsGraph with
            | Result.Error reason ->
                Assert.Equal("Boundary buffer, borrowed-handle, and borrowed-view calls require their exact direct signature and complete ordered actuals.", reason)
            | Result.Ok other -> failwithf "Admitted indirect BufferAbsence call: %A" other
            let badRoDescGraph =
                { graph with
                    Emission =
                        { graph.Emission with
                            Boundary =
                                { graph.Emission.Boundary with
                                    ReadOnlyBufferDeclarations = Map.ofList [ roId, { roDecl with Descriptor = id 999 } ] } } }
            match runBoundaryCallAt siteId badRoDescGraph with
            | Result.Error reason ->
                Assert.Equal("Optional byte-buffer absence conversion at boundary call 260 operand 0 lacks its exact BufferAbsenceContract or claim.", reason)
            | Result.Ok other -> failwithf "Admitted BufferAbsence Direct(None) with mismatched ReadOnlyBufferDeclarations descriptor: %A" other

    [<Fact>]
    let ``BorrowedResultView emits deferred BoundaryBufferCall with CompanionCall and borrowed ResourceHandle call emits FuncCall`` () =
        let bvId = id 350
        let declBinding = id 351
        let bodyId = id 352
        let descId = id 353
        let ownerFormal = id 354
        let siteId = id 360
        let calleeId = id 361
        let ownerActual = id 0
        let invId = id 362
        let readId = id 363
        let scopeClaimId = id 364
        let compSiteId = id 365
        let compImportId = id 366
        let support = Set.ofList [ bvId; declBinding; bodyId; descId; ownerFormal; siteId; calleeId; ownerActual; invId; readId; scopeClaimId; compSiteId; compImportId ]
        let descFacts =
            let pCase = id 980
            let arrId = id 981
            Map.ofList
                [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                  ownerFormal, { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
                  arrId, { emptyFact "array" with References = [ ownerFormal ]; Children = [ ownerFormal ] }
                  descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let bvDecl : BoundaryBorrowedResultViewDeclaration =
            { Identity = bvId; Declaration = declBinding; Body = bodyId; Formals = [ ownerFormal ]; Descriptor = descId
              OwnerParameter = 0; OwnerFormal = ownerFormal
              Contract =
                { Binding = "Fixture.columnText"; Owner = 0
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Extent = BAREWire.Descriptors.BorrowedExtent.CompanionCall("Fixture.columnBytes", [| 0 |])
                  InvalidatedBy =
                    [| BAREWire.Descriptors.BorrowInvalidation.OwnerCall { Binding = "Fixture.step"; Parameter = 0 }
                       BAREWire.Descriptors.BorrowInvalidation.OwnerCall { Binding = "Fixture.finalize"; Parameter = 0 } |]
                  Hypothesis = { Identity = "fixture.bv"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let mkUse (nullToNone: bool) (readOrder: int) (withCompanion: bool) : BoundaryBorrowedResultViewUse =
            { Call = siteId; Declaration = bvId; Owner = ownerActual; View = siteId
              CompanionCall = (if withCompanion then Some compSiteId else None)
              CompanionArguments = (if withCompanion then [ ownerActual ] else [])
              CallOrder = 10; Invalidations = [ invId ]; InvalidationOrders = [ 20 ]
              Reads = [ readId ]; ReadOrders = [ readOrder ]; NullToNoneBoundary = nullToNone
              ScopeProof = scopeClaimId; Participants = ParticipantEvidence.Established [] }
        let mkScopeOb (nullToNone: bool) (readOrder: int) =
            obligation scopeClaimId "foreign-borrowed-view-scope"
                (ObligationBody.BorrowedResultViewScope
                    { Call = siteId; Declaration = bvId; Owner = ownerActual; View = siteId
                      CallOrder = 10; InvalidationOrders = [ 20 ]; ReadOrders = [ readOrder ]
                      NullToNoneBoundary = nullToNone })
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding
              Library = "fixture"; Symbol = "fixture_column_text"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]; Parameters = [ ownerFormal, BoundaryScalar.ResourceHandle(ownerFormal, false) ]
              Result = Some(BoundaryScalar.BorrowedBytes bvId)
              Participants = support
              SourceTypes = Map.ofList [ ownerFormal, ptrHandleType ]
              DeclarationFacts = descFacts.Add(ownerFormal, { descFacts[ownerFormal] with SourceType = ptrHandleType }) }
        let compImport : BoundaryImport =
            { Identity = compImportId; Binding = id 367; Scope = id 367
              Library = "fixture"; Symbol = "fixture_column_bytes"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ id 367 ]; Parameters = [ ownerFormal, BoundaryScalar.ResourceHandle(ownerFormal, false) ]
              Result = Some(BoundaryScalar.Integer(32, true)); Participants = Set.empty; SourceTypes = Map.empty; DeclarationFacts = Map.empty }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments = [ { Actual = ownerActual; Formal = ownerFormal; Abi = BoundaryScalar.ResourceHandle(ownerFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.BorrowedBytes bvId); ResultAdaptation = None
              Participants = support; SourceTypes = Map.empty }
        let compCall : BoundaryCall =
            { Site = compSiteId; Import = compImportId; Callee = id 368; Entry = None; Resource = None
              Arguments = [ { Actual = ownerActual; Formal = ownerFormal; Abi = BoundaryScalar.ResourceHandle(ownerFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.Integer(32, true)); ResultAdaptation = None
              Participants = Set.empty; SourceTypes = Map.empty }
        let build (nullToNone: bool) (readOrder: int) (withCompanion: bool) =
            let ob = mkScopeOb nullToNone readOrder
            let emptyGraph = revision []
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ ownerActual ])) [ calleeId; ownerActual ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_column_text", Some declBinding)) []
                          ownerActual, mkNode ownerActual ptrHandleType (SemanticKind.VarRef("stmt", None)) []
                          scopeClaimId, mkNode scopeClaimId unitType (SemanticKind.Obligation ob) [] ]
                Obligations = [ ob ]
                Emission =
                    { emptyGraph.Emission with
                        Callable = { emptyGraph.Emission.Callable with AliasTargets = Map.ofList [ siteId, siteId ] }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ ownerActual, Result.Ok handleRep
                                          ownerFormal, Result.Ok handleRep
                                          siteId, Result.Ok bufRep ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow; compImportId, compImport ]
                                ByScope = Map.ofList [ declBinding, [ descId ] ]
                                Calls = Map.ofList [ siteId, callRow; compSiteId, compCall ]
                                BorrowedResultViewDeclarations = Map.ofList [ bvId, bvDecl ]
                                BorrowedResultViewUses = Map.ofList [ siteId, mkUse nullToNone readOrder withCompanion ] } } }

        let validGraph = build true 12 true
        match runBoundaryCallAt siteId validGraph with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 360, [ { Type = TOpaqueHandle _ } ], [], [], [ { Type = TMemRef(TInt(IntWidth 8)) } ]) ] as ops, TRValue _), _) ->
            match Alex.Patterns.PlatformPatterns.boundaryImportsAt declBinding validGraph.Emission.Boundary with
            | Result.Ok([ MLIROp.ResourceImport _ ] as decls) ->
                Assert.Equal(Result.Ok NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None decls)
                Assert.Equal(Result.Ok NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None ops)
            | other -> failwithf "Unexpected boundaryImportsAt result: %A" other
        | other -> failwithf "Unexpected BorrowedResultView positive result: %A" other

        // Plain borrowed ResourceHandle argument (call.Resource.IsNone) returning i32 emits FuncCall
        let plainBorrowedCall = { callRow with Result = Some(BoundaryScalar.Integer(32, true)) }
        let plainBorrowedImport = { importRow with Symbol = "fixture_column_bytes"; Result = Some(BoundaryScalar.Integer(32, true)) }
        let plainBorrowedGraph =
            { validGraph with
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId intType (SemanticKind.Application(calleeId, [ ownerActual ])) [ calleeId; ownerActual ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_column_bytes", Some declBinding)) []
                          ownerActual, mkNode ownerActual ptrHandleType (SemanticKind.VarRef("stmt", None)) [] ]
                Obligations = []
                Emission =
                    { validGraph.Emission with
                        Numeric =
                            { validGraph.Emission.Numeric with
                                OccurrenceRepresentations =
                                    validGraph.Emission.Numeric.OccurrenceRepresentations.Add(siteId, Result.Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32")))) }
                        Boundary =
                            { validGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, plainBorrowedImport ]
                                Calls = Map.ofList [ siteId, plainBorrowedCall ] } } }
        match runBoundaryCallAt siteId plainBorrowedGraph with
        | Result.Ok(([ MLIROp.FuncOp(FuncOp.FuncCall([ { Type = TInt(IntWidth 32) } ], "fixture_column_bytes", [ { Type = TOpaqueHandle(_, 64, 8) } ])) ], TRValue _), _) -> ()
        | other -> failwithf "Unexpected plain borrowed ResourceHandle result: %A" other

        // Negative control: mismatched handle identity on borrowed ResourceHandle must fail without widening
        let otherHandleType =
            TypeIdentity.Application(
                { Declaration = { Module = [ "Fixture" ]; Name = "WrongHandle" }
                  Parameters = [ TypeParamKind.Type ]
                  NativeKind = Some NTUKind.NTUptr },
                [ unitType ])
        let wrongHandleRep = ValueRepresentation.Scalar(SettledSlot.CHandle(otherHandleType, 64, 8))
        let wrongHandleGraph =
            { plainBorrowedGraph with
                Emission =
                    { plainBorrowedGraph.Emission with
                        Numeric =
                            { plainBorrowedGraph.Emission.Numeric with
                                OccurrenceRepresentations =
                                    plainBorrowedGraph.Emission.Numeric.OccurrenceRepresentations.Add(ownerActual, Result.Ok wrongHandleRep) } } }
        match runBoundaryCallAt siteId wrongHandleGraph with
        | Result.Error reason -> Assert.Equal("Borrowed resource argument disagrees with its source handle carrier.", reason)
        | Result.Ok other -> failwithf "Admitted mismatched borrowed ResourceHandle type: %A" other

        // D1 negative controls: withdrawn or omitted occurrence representations return Result.Error cleanly (never throw failwith)
        let withdrawnViewGraph =
            { validGraph with
                Emission =
                    { validGraph.Emission with
                        Numeric =
                            { validGraph.Emission.Numeric with
                                OccurrenceRepresentations =
                                    validGraph.Emission.Numeric.OccurrenceRepresentations.Add(siteId, Result.Error "withdrawn view") } } }
        match runBoundaryCallAt siteId withdrawnViewGraph with
        | Result.Error reason ->
            Assert.Equal("TypeMapping: value occurrence 360 has no source-published representation: withdrawn view", reason)
        | Result.Ok other -> failwithf "Admitted BorrowedBytes result with withdrawn occurrence representation: %A" other

        let omittedViewGraph =
            { validGraph with
                Emission =
                    { validGraph.Emission with
                        Numeric =
                            { validGraph.Emission.Numeric with
                                OccurrenceRepresentations =
                                    validGraph.Emission.Numeric.OccurrenceRepresentations.Remove siteId } } }
        match runBoundaryCallAt siteId omittedViewGraph with
        | Result.Error reason ->
            Assert.Equal("TypeMapping: source publication omitted value occurrence 360", reason)
        | Result.Ok other -> failwithf "Admitted BorrowedBytes result with omitted occurrence representation: %A" other

        let withdrawnOwnerGraph =
            { plainBorrowedGraph with
                Emission =
                    { plainBorrowedGraph.Emission with
                        Numeric =
                            { plainBorrowedGraph.Emission.Numeric with
                                OccurrenceRepresentations =
                                    plainBorrowedGraph.Emission.Numeric.OccurrenceRepresentations.Add(ownerActual, Result.Error "withdrawn owner") } } }
            |> declareTraversalReadings
        let accWithdrawnOwner = MLIRAccumulator.empty ()
        MLIRAccumulator.bindNode ownerActual (Arg 0) (Alex.CodeGeneration.TypeMapping.representationType handleRep |> Result.defaultWith failwith) accWithdrawnOwner
        match matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus withdrawnOwnerGraph withdrawnOwnerGraph.Nodes[siteId]) 64 accWithdrawnOwner with
        | Result.Error reason ->
            Assert.Equal("TypeMapping: value occurrence 0 has no source-published representation: withdrawn owner", reason)
            Assert.Empty accWithdrawnOwner.AllOps
            Assert.True((MLIRAccumulator.recallNode siteId accWithdrawnOwner).IsNone)
        | Result.Ok other -> failwithf "Admitted ResourceHandle argument with withdrawn occurrence representation: %A" other

        // Negative controls: scope claim mismatch, nullToNone=false, missing companion, borrowedBytes as argument
        let mismatchedScopeGraph =
            let badOb = mkScopeOb true 99
            { validGraph with
                Nodes = Map.add scopeClaimId (mkNode scopeClaimId unitType (SemanticKind.Obligation badOb) []) validGraph.Nodes
                Obligations = [ badOb ] }
        for badGraph in [ mismatchedScopeGraph; build false 12 true; build true 12 false ] do
            match runBoundaryCallAt siteId badGraph with
            | Result.Error reason ->
                Assert.Equal("Borrowed result view at boundary call 360 lacks its exact non-owning declaration, invalidation frontier, or scope claim.", reason)
            | Result.Ok other -> failwithf "Admitted invalid BorrowedResultView use: %A" other

        let badArgCall =
            { callRow with
                Arguments = [ { Actual = ownerActual; Formal = ownerFormal; Abi = BoundaryScalar.BorrowedBytes bvId; Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
                Result = None }
        let badArgImport = { importRow with Parameters = [ ownerFormal, BoundaryScalar.BorrowedBytes bvId ]; Result = None }
        let badArgGraph =
            { validGraph with
                Emission =
                    { validGraph.Emission with
                        Boundary =
                            { validGraph.Emission.Boundary with
                                Imports = validGraph.Emission.Boundary.Imports.Add(descId, badArgImport)
                                Calls = validGraph.Emission.Boundary.Calls.Add(siteId, badArgCall) } } }
        match runBoundaryCallAt siteId badArgGraph with
        | Result.Error reason -> Assert.Equal("Borrowed result view cannot appear as a boundary call argument.", reason)
        | Result.Ok other -> failwithf "Admitted BorrowedBytes as boundary call argument: %A" other

        Assert.True((BoundaryAbi.scalarType (BoundaryScalar.ReadOnlyBytes bvId)).IsError)
        Assert.True((BoundaryAbi.scalarType (BoundaryScalar.BorrowedBytes bvId)).IsError)

    [<Fact>]
    let ``CountedEntryArrays and Retained callback extent emit native entry parameter types and refuse invalid Retained bounds`` () =
        let countedId = id 450
        let invId = id 451
        let importId = id 452
        let entryId = id 453
        let ctxFormal = id 454
        let argcFormal = id 455
        let argvFormal = id 456
        let implId = id 457
        let bodyId = id 458
        let cbFormal = id 460
        let fnPtrCHandleType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [ TypeParamKind.Type ]; NativeKind = Some NTUKind.NTUfnptr },
                [ TypeIdentity.Function(TypeIdentity.Tuple(false, [ ptrHandleType; intType; uint8Type ]), unitType) ])
        let countedRow : BoundaryCountedEntryArray =
            { Identity = countedId; Import = importId; Parameter = 0; Invocation = invId
              Contract =
                { Binding = "Fixture.xFunc"; Parameter = 5; Argument = 2; CountArgument = 1
                  Element = BAREWire.Descriptors.CountedElement.Handle "sqlite3_value*" }
              DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let mkInvocation (owner: int) (releases: BAREWire.Descriptors.RetentionRelease seq) : BoundaryCallbackInvocation =
            { Identity = invId; Import = importId; Parameter = 5; Formal = cbFormal; Scope = id 464
              Contract =
                { Binding = "Fixture.createFn"; Parameter = 5
                  Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters =
                        [| { Name = "ctx"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Void }
                  Hypothesis = { Identity = "fixture.retcb"; Version = "1"; Source = "component contract" } }
              Signature =
                { CallingConvention = "CDecl"
                  Parameters =
                    [ BoundaryScalar.ResourceHandle(cbFormal, false)
                      BoundaryScalar.Integer(32, true)
                      BoundaryScalar.ReadOnlyBytes countedId ]
                  Result = None }
              Extent = BoundaryCallbackExtent.Retained(owner, Array.ofSeq releases)
              Participants = Set.singleton invId }
        let cbImport : BoundaryImport =
            { Identity = importId; Binding = id 462; Scope = id 462
              Library = "fixture"; Symbol = "fixture_create_fn"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ id 462 ]; Parameters = [ cbFormal, BoundaryScalar.Entry invId ]
              Result = None; Participants = Set.ofList [ importId; cbFormal; invId ]
              SourceTypes = Map.ofList [ cbFormal, fnPtrCHandleType ]
              DeclarationFacts = Map.ofList [ cbFormal, { emptyFact "binding" with Text = [ "xFunc" ]; SourceType = fnPtrCHandleType } ] }
        let emptyGraph = revision []
        let baseBoundary = emptyGraph.Emission.Boundary
        let releaseOne = BAREWire.Descriptors.RetentionRelease.OwnerRelease { Binding = "Fixture.close"; Parameter = 0 }
        let boundary =
            { baseBoundary with
                Imports = Map.ofList [ importId, cbImport ]
                CountedEntryArrays = Map.ofList [ countedId, countedRow ]
                CallbackInvocations = Map.ofList [ invId, mkInvocation 0 [ releaseOne ] ] }
        Assert.Equal(
            Result.Error "A read-only byte carrier lacks its exact source-published declaration.",
            BoundaryAbi.tryScalarTypeIn boundary Set.empty (BoundaryScalar.ReadOnlyBytes countedId))

        let entry : BoundaryClosedEntry =
            { Formation = entryId; Operand = id 461; Declaration = id 462; Implementation = implId
              Formals = [ ctxFormal; argcFormal; argvFormal ]; Body = bodyId
              Lifetime = { Module = id 462; Binding = id 462; Implementation = implId }
              Invocation = invId; ParameterAdaptations = [ None; None; None ]; ResultAdaptation = None
              Registrations = Map.empty; Transport = Set.singleton entryId; Participants = Set.singleton entryId }
        let decl : CallableEmissionDeclaration =
            { Lookup = implId; Implementation = implId
              Parameters = [ "ctx", ptrHandleType, ctxFormal; "argc", intType, argcFormal; "argv", uint8Type, argvFormal ]
              Result = bodyId; Context = LambdaContext.RegularClosure; Captures = []
              Name = CallableSymbolName.ModuleBinding("Fixture", "xFunc"); Parent = None; Participants = Set.empty }
        let siteId = id 463
        let directCallProof : CallableEmissionCall =
            { Site = siteId; Implementation = implId; Parameters = decl.Parameters
              Arguments = [ ctxFormal; argcFormal; argvFormal ]; Result = bodyId
              SignatureData = Set.empty; Participants = Set.empty }
        let dummyFnType = TypeIdentity.Function(ptrHandleType, unitType)
        let mkTestGraph (owner: int) (releases: BAREWire.Descriptors.RetentionRelease array) =
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(implId, [ ctxFormal; argcFormal; argvFormal ])) [ implId; ctxFormal; argcFormal; argvFormal ]
                          implId, mkNode implId dummyFnType (SemanticKind.Lambda([ "ctx", ptrHandleType, ctxFormal ], bodyId, [], None, LambdaContext.RegularClosure)) [ bodyId ]
                          ctxFormal, mkNode ctxFormal ptrHandleType (SemanticKind.PatternBinding "ctx") []
                          argcFormal, mkNode argcFormal intType (SemanticKind.PatternBinding "argc") []
                          argvFormal, mkNode argvFormal uint8Type (SemanticKind.PatternBinding "argv") []
                          bodyId, mkNode bodyId unitType (SemanticKind.VarRef("unitBody", None)) [] ]
                Emission =
                    { emptyGraph.Emission with
                        Boundary =
                            { boundary with
                                CallbackInvocations = Map.ofList [ invId, mkInvocation owner releases ]
                                ClosedEntries = Map.ofList [ entryId, entry ] }
                        Callable =
                            { emptyGraph.Emission.Callable with
                                Declarations = Map.ofList [ implId, decl ]
                                NativeEntries = Map.ofList [ implId, "xFunc_native" ]
                                UnitNodes = Set.singleton bodyId
                                Calls = Map.ofList [ siteId, directCallProof ]
                                ValueShapes = Map.ofList [ ctxFormal, CallableValueShape.Data ctxFormal ]
                                ClosedData = Set.singleton ctxFormal }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ ctxFormal, Result.Ok handleRep
                                          bodyId, Result.Ok(ValueRepresentation.Scalar SettledSlot.Unit) ] } } }
            |> declareTraversalReadings

        let mkCtx (g: Revision) : WitnessContext =
            let acc = MLIRAccumulator.empty ()
            let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
            let visited = ref Set.empty
            { Coeffects = coeffects 64; Accumulator = acc; RootAccumulator = acc
              ScopeContext = scope; RootScopeContext = scope; Graph = g
              Zipper = focus g g.Nodes[siteId]; GlobalVisited = visited; TraversalVisited = visited }

        let goodGraph = mkTestGraph 0 [| releaseOne |]
        match Alex.Traversal.CallableOperands.parametersAtCall (mkCtx goodGraph) siteId implId decl.Parameters with
        | Result.Ok [ [ TOpaqueHandle(_, 64, 8) ]; [ TInt(IntWidth 32) ]; [ TMemRef(TInt(IntWidth 8)) ] ] -> ()
        | other -> failwithf "Unexpected Retained callback parametersAtCall result: %A" other

        // Negative controls: owner = invocation.Parameter (5) and empty releases array must fail with exact reason
        for badGraph in [ mkTestGraph 5 [| releaseOne |]; mkTestGraph 0 [||] ] do
            let badCtx = mkCtx badGraph
            match Alex.Traversal.CallableOperands.parametersAtCall badCtx siteId implId decl.Parameters with
            | Result.Error reason ->
                Assert.Equal("Closed native callback extent lacks its exact finite registration account.", reason)
                Assert.Empty badCtx.Accumulator.AllOps
                Assert.True((MLIRAccumulator.recallNode siteId badCtx.Accumulator).IsNone)
            | Result.Ok other -> failwithf "Admitted malformed Retained callback extent: %A" other

    /// Mixed direct call (`sqlite3_exec` shape: borrowed CHandle + ReadOnlyBytes +
    /// direct OptionalEntry callback + direct BufferAbsence output) witnesses one
    /// BoundaryBufferCall retaining all operand slots, while indirect call.Entry.IsSome refuses.
    [<Fact>]
    let ``mixed sqlite3_exec direct boundary call witnesses BoundaryBufferCall with both slot kinds and refuses indirect`` () =
        let declBinding = id 650
        let descId = id 651
        let dbFormal = id 652
        let sqlFormal = id 653
        let cbFormal = id 654
        let errFormal = id 655
        let roId = id 656
        let invId = id 657
        let entryNodeId = id 658
        let absQuoteId = id 659
        let siteId = id 660
        let calleeId = id 661
        let dbActual = id 0
        let sqlActual = id 1
        let cbActual = id 662
        let errActual = id 663
        let cbFormId = id 664
        let cbBodyId = id 665
        let resId = id 666
        let termClaimId = id 667
        let retClaimId = id 668
        let entryClaimId = id 669
        let absClaimId = id 670
        let support =
            Set.ofList
                [ declBinding; descId; dbFormal; sqlFormal; cbFormal; errFormal; roId; invId
                  absQuoteId; siteId; calleeId; dbActual; sqlActual; cbActual; errActual
                  cbFormId; cbBodyId; resId; termClaimId; retClaimId; entryClaimId; absClaimId ]
        let descFacts =
            let pCase = id 990
            let arrId = id 991
            let pRec = { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
            Map.ofList
                [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                  dbFormal, { pRec with SourceType = ptrHandleType }
                  sqlFormal, pRec
                  cbFormal, pRec
                  errFormal, pRec
                  arrId, { emptyFact "array" with References = [ dbFormal; sqlFormal; cbFormal; errFormal ]; Children = [ dbFormal; sqlFormal; cbFormal; errFormal ] }
                  descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let roDecl : BoundaryReadOnlyBufferDeclaration =
            { Identity = roId; Declaration = declBinding; Body = id 671; Formals = [ dbFormal; sqlFormal; cbFormal; errFormal ]; Descriptor = descId
              Parameter = 1; CountParameter = None; BufferFormal = sqlFormal; CountFormal = None
              Contract =
                { Binding = "Fixture.exec"; Parameter = 1
                  Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                  Hypothesis = { Identity = "fixture.exec.sql"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let errRoId = id 678
        let errRoDecl : BoundaryReadOnlyBufferDeclaration =
            { roDecl with
                Identity = errRoId
                Parameter = 3
                BufferFormal = errFormal }
        let roUse : BoundaryReadOnlyBufferUse =
            { Call = siteId; Declaration = roId; Parameter = 1; Buffer = sqlActual; Residence = resId
              Retirements = []; Copies = 0
              Crossing = BoundaryReadOnlyBufferCrossing.StaticImageNulBorrowed(0, sqlActual, 2I, termClaimId)
              RetentionProof = retClaimId; AccessExclusivityProof = None; Participants = ParticipantEvidence.Established [] }
        let termOb =
            obligation termClaimId "foreign-uncounted-path-termination"
                (ObligationBody.UncountedPathTermination
                    { Call = siteId; Declaration = roId; Parameter = 1; Source = sqlActual; ByteLength = 2I
                      Mode = UncountedPathStagingMode.StaticImageZeroCopy 0
                      RequiresNoInteriorNul = true; RequiresTrailingNul = true })
        let retOb =
            obligation retClaimId "foreign-buffer-retention-domination"
                (ObligationBody.BufferRetentionDomination
                    { Call = siteId; Declaration = roId; Buffer = sqlActual; Residence = resId
                      Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
        let fnType = functionFrom intType intType
        let fnPtrType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [ TypeParamKind.Type ]; NativeKind = Some NTUKind.NTUfnptr },
                [ fnType ])
        let optFnType = optionOf fnPtrType
        let optFnRep = ValueRepresentation.Union([ "None", []; "Some", [ ValueRepresentation.Scalar(SettledSlot.Integer(64, None)) ] ], Some(0, 16, 8))
        let cbInv : BoundaryCallbackInvocation =
            { Identity = invId; Import = descId; Parameter = 2; Formal = cbFormal; Scope = id 672
              Contract =
                { Binding = "Fixture.exec"; Parameter = 2; Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters = [| { Name = "x"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32) }
                  Hypothesis = { Identity = "fixture.exec.cb"; Version = "1"; Source = "component contract" } }
              Signature = { CallingConvention = "CDecl"; Parameters = [ BoundaryScalar.Integer(32, true) ]; Result = Some(BoundaryScalar.Integer(32, true)) }
              Extent = BoundaryCallbackExtent.DuringCall; Participants = Set.singleton invId }
        let entryOb =
            obligation entryClaimId "foreign-optional-entry-conversion-2"
                (ObligationBody.OptionalEntryArgumentConversion
                    { Call = siteId; Parameter = 2; Actual = cbActual; Construction = cbActual; SourceCase = 1
                      Payload = cbFormId; Formation = cbFormId; Invocation = invId; ResultRetirement = None
                      Arms = [ { CaseOrdinal = 0; Choice = OptionalEntryPlanChoice.PendingAbsence; Formation = None }
                               { CaseOrdinal = 1; Choice = OptionalEntryPlanChoice.ClosedEntry; Formation = Some cbFormId } ] })
        let optEntrySel : BoundaryOptionalEntry =
            { Construction = cbActual; CaseOrdinal = 1; Payload = Some cbFormId; Formation = Some cbFormId; Transport = Set.ofList [ cbActual ]; Obligation = entryClaimId }
        let absRow : BoundaryBufferAbsence =
            { Quote = absQuoteId; DescriptorBinding = id 673; Record = id 674; Import = descId; Parameter = 3; Formal = errFormal
              BufferDeclaration = errRoId; Contract = { Binding = "Fixture.exec"; Parameter = 3; Hypothesis = { Identity = "fixture.exec.err"; Version = "1"; Source = "component contract" } }
              SourcePath = []; Inputs = []; DeclarationFacts = Map.empty }
        let absOb =
            obligation absClaimId "foreign-buffer-absence-conversion-3"
                (ObligationBody.BufferAbsenceArgumentConversion
                    { Call = siteId; Parameter = 3; Actual = errActual; Construction = errActual; SourceCase = 0; Absence = absQuoteId
                      Arms = [ { CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
                               { CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer } ] })
        let absSel : BoundaryBufferAbsenceSelection =
            { Construction = errActual; CaseOrdinal = 0; Payload = None; Absence = absQuoteId; Transport = [ errActual ]; Obligation = absClaimId }
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding; Library = "fixture"; Symbol = "fixture_exec"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]
              Parameters =
                [ dbFormal, BoundaryScalar.ResourceHandle(dbFormal, false)
                  sqlFormal, BoundaryScalar.ReadOnlyBytes roId
                  cbFormal, BoundaryScalar.Entry invId
                  errFormal, BoundaryScalar.ReadOnlyBytes errRoId ]
              Result = Some(BoundaryScalar.Integer(32, true)); Participants = support
              SourceTypes = Map.ofList [ dbFormal, ptrHandleType ]; DeclarationFacts = descFacts }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments =
                [ { Actual = dbActual; Formal = dbFormal; Abi = BoundaryScalar.ResourceHandle(dbFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = sqlActual; Formal = sqlFormal; Abi = BoundaryScalar.ReadOnlyBytes roId; Adaptation = None; OptionalEntry = None; BufferAbsence = None }
                  { Actual = cbActual; Formal = cbFormal; Abi = BoundaryScalar.Entry invId; Adaptation = None; OptionalEntry = Some(BoundaryOptionalEntryChoice.Direct optEntrySel); BufferAbsence = None }
                  { Actual = errActual; Formal = errFormal; Abi = BoundaryScalar.ReadOnlyBytes errRoId; Adaptation = None; OptionalEntry = None; BufferAbsence = Some(BoundaryBufferAbsenceChoice.Direct absSel) } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.Integer(32, true)); ResultAdaptation = None
              Participants = support; SourceTypes = Map.empty }
        let carrier : CallableCarrier =
            { Occurrence = cbFormId; Kind = CallableKind.NativeEntry; Formation = cbFormId; EnvironmentValue = None
              Contract = Result.Ok(id 677); Lifetime = []; SourceType = fnPtrType; Implementation = cbBodyId
              Parameters = [ "x", intType, id 675 ]; Result = id 676
              ParameterShapes = [ CallableValueShape.Data(id 675) ]; ResultShape = CallableValueShape.Data(id 676)
              OmittedParameters = Set.empty; Environment = None }
        let closedEntry : BoundaryClosedEntry =
            { Formation = cbFormId; Operand = cbFormId; Declaration = id 677; Implementation = cbBodyId
              Formals = [ id 675 ]; Body = id 676
              Lifetime = { Module = id 677; Binding = id 677; Implementation = cbBodyId }
              Invocation = invId; ParameterAdaptations = [ None ]; ResultAdaptation = None
              Registrations = Map.empty; Transport = Set.singleton cbFormId; Participants = Set.singleton cbFormId }
        let declRow : CallableEmissionDeclaration =
            { Lookup = cbBodyId; Implementation = cbBodyId; Parameters = [ "x", intType, id 675 ]; Result = id 676
              Context = LambdaContext.RegularClosure; Captures = []
              Name = CallableSymbolName.ModuleBinding("Fixture", "cb"); Parent = None; Participants = Set.empty }
        let pool : StaticStringPool =
            { Symbol = ".rodata.str"; Bytes = [ 104uy; 105uy; 0uy ]; Alignment = 1; Size = 3; UsedSize = 3
              Entries = [ { Content = "hi"; Offset = 0; Length = 2; StorageLength = 3; NodeIds = [ sqlActual ] } ]
              SpaceName = "rodata"; Capacity = 16L; SpaceAlignment = 1; Granularity = 1; DeclarationNode = declBinding }
        let emptyGraph = revision []
        let graph =
            { emptyGraph with
                StaticStringPool = Some pool
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId intType (SemanticKind.Application(calleeId, [ dbActual; sqlActual; cbActual; errActual ])) [ calleeId; dbActual; sqlActual; cbActual; errActual ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_exec", Some declBinding)) []
                          dbActual, mkNode dbActual ptrHandleType (SemanticKind.VarRef("db", None)) []
                          sqlActual, mkNode sqlActual unitType (SemanticKind.VarRef("sql", None)) []
                          cbActual, mkNode cbActual optFnType (SemanticKind.VarRef("cbOpt", None)) []
                          errActual, mkNode errActual unitType (SemanticKind.VarRef("errOpt", None)) []
                          cbFormId, mkNode cbFormId fnPtrType (SemanticKind.VarRef("cbFn", None)) []
                          termClaimId, mkNode termClaimId unitType (SemanticKind.Obligation termOb) []
                          retClaimId, mkNode retClaimId unitType (SemanticKind.Obligation retOb) []
                          entryClaimId, mkNode entryClaimId unitType (SemanticKind.Obligation entryOb) []
                          absClaimId, mkNode absClaimId unitType (SemanticKind.Obligation absOb) [] ]
                Obligations = [ termOb; retOb; entryOb; absOb ]
                Emission =
                    { emptyGraph.Emission with
                        Callable =
                            { emptyGraph.Emission.Callable with
                                Declarations = Map.ofList [ cbBodyId, declRow ]
                                Carriers = Map.ofList [ cbFormId, carrier ]
                                Symbols = Map.ofList [ cbBodyId, CallableSymbolName.ModuleBinding("Fixture", "cb") ]
                                NativeEntries = Map.ofList [ cbBodyId, "Fixture.cb" ]
                                ValueShapes = Map.ofList [ id 675, CallableValueShape.Data(id 675); id 676, CallableValueShape.Data(id 676) ]
                                ClosedData = Set.ofList [ id 675; id 676 ]
                                AliasTargets = Map.ofList [ siteId, siteId ] }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ dbActual, Result.Ok handleRep
                                          dbFormal, Result.Ok handleRep
                                          sqlActual, Result.Ok bufRep
                                          cbActual, Result.Ok optFnRep
                                          errActual, Result.Ok optBufRep
                                          id 675, Result.Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32")))
                                          id 676, Result.Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32")))
                                          siteId, Result.Ok(ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32"))) ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow ]
                                Calls = Map.ofList [ siteId, callRow ]
                                ReadOnlyBufferDeclarations = Map.ofList [ roId, roDecl; errRoId, errRoDecl ]
                                ReadOnlyBufferUses = Map.ofList [ (siteId, 1), roUse ]
                                CallbackInvocations = Map.ofList [ invId, cbInv ]
                                ClosedEntries = Map.ofList [ cbFormId, closedEntry ]
                                BufferAbsences = Map.ofList [ absQuoteId, absRow ] } } }
        let runMixed g =
            let g' = declareTraversalReadings g
            let acc = MLIRAccumulator.empty ()
            for (nid, repRes) in Map.toList g'.Emission.Numeric.OccurrenceRepresentations do
                match repRes with
                | Result.Ok rep when nid <> siteId ->
                    MLIRAccumulator.bindNode nid (V(NodeId.value nid, 0)) (Alex.CodeGeneration.TypeMapping.representationType rep |> Result.defaultWith failwith) acc
                | _ -> ()
            MLIRAccumulator.bindNode cbFormId (V(NodeId.value cbFormId, 0)) (TFunc([ TInt(IntWidth 32) ], [ TInt(IntWidth 32) ])) acc
            let r = matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus g' g'.Nodes[siteId]) 64 acc
            Assert.Empty acc.AllOps
            Assert.True((MLIRAccumulator.recallNode siteId acc).IsNone)
            r

        match runMixed graph with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 660, vals, [ { Ordinal = 2 } ], [ { BufferOrdinal = 3 } ], [ { Type = TInt(IntWidth 32) } ]) ], TRValue _), _) ->
            Assert.Equal(4, vals.Length)
        | other -> failwithf "Unexpected mixed sqlite3_exec-shape BoundaryBufferCall result: %A" other

        let indirectGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                Calls = Map.ofList [ siteId, { callRow with Entry = Some entryNodeId } ] } } }
        match runMixed indirectGraph with
        | Result.Error reason ->
            Assert.Equal("Boundary buffer, borrowed-handle, and borrowed-view calls require their exact direct signature and complete ordered actuals.", reason)
        | Result.Ok other -> failwithf "Admitted indirect mixed boundary call: %A" other

    [<Fact>]
    let ``SMTTransfer transcribes all five Schema 53 obligation bodies to portable QF_LIA scopes and rejects F#-folded arm checks`` () =
        let arm0 = { CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
        let arm1 = { CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer }
        let obs =
            [ obligation (id 501) "foreign-readonly-buffer-extent"
                (ObligationBody.ZeroCopyBufferExtent
                    { Call = id 1; Declaration = id 2; Parameter = 1; CountParameter = 2
                      Buffer = id 3; Count = id 4; MinimumCount = 1I; MaximumCount = 8I; ExtentCapacity = 16I
                      ElementBytes = 1; CountCoverage = id 501 })
              obligation (id 502) "foreign-buffer-retention-domination"
                (ObligationBody.BufferRetentionDomination
                    { Call = id 1; Declaration = id 2; Buffer = id 3; Residence = id 5
                      Mode = BufferRetentionMode.RetainedUntilOwner(0, 1); AcquireOrder = 1; RetirementOrders = [ 10 ] })
              obligation (id 503) "foreign-uncounted-path-termination"
                (ObligationBody.UncountedPathTermination
                    { Call = id 1; Declaration = id 2; Parameter = 0; Source = id 3; ByteLength = 5I
                      Mode = UncountedPathStagingMode.CallScopedStaged(id 6, 6)
                      RequiresNoInteriorNul = true; RequiresTrailingNul = true })
              obligation (id 504) "foreign-borrowed-view-scope"
                (ObligationBody.BorrowedResultViewScope
                    { Call = id 1; Declaration = id 2; Owner = id 7; View = id 1
                      CallOrder = 2; InvalidationOrders = [ 20 ]; ReadOrders = [ 5 ]; NullToNoneBoundary = true })
              obligation (id 505) "foreign-buffer-absence-conversion-0"
                (ObligationBody.BufferAbsenceArgumentConversion
                    { Call = id 1; Parameter = 0; Actual = id 8; Construction = id 8
                      SourceCase = 1; Absence = id 9
                      Arms = [ arm0; arm1 ] }) ]
        let mlir = Alex.Traversal.SMTTransfer.transfer obs |> Result.defaultWith failwith
        let expectedMlir =
            String.concat "\n"
                [ "module @obligations {"
                  "  // ob_501: fixture obligation"
                  "  // origin: Fixture.clef:1:1"
                  "  smt.solver () : () -> () {"
                  "    smt.set_logic \"QF_LIA\""
                  "    %v0_5 = smt.int.constant 0"
                  "    %v0_6 = smt.int.constant 1"
                  "    %v0_7 = smt.int.cmp le %v0_5, %v0_6"
                  "    %v0_8 = smt.int.constant 1"
                  "    %v0_9 = smt.int.constant 8"
                  "    %v0_10 = smt.int.cmp le %v0_8, %v0_9"
                  "    %v0_0 = smt.int.constant 8"
                  "    %v0_1 = smt.int.constant 1"
                  "    %v0_2 = smt.int.mul %v0_0, %v0_1"
                  "    %v0_3 = smt.int.constant 16"
                  "    %v0_4 = smt.int.cmp le %v0_2, %v0_3"
                  "    %v0_11 = smt.int.constant 1"
                  "    %v0_12 = smt.int.constant 0"
                  "    %v0_13 = smt.int.cmp gt %v0_11, %v0_12"
                  "    %v0_14 = smt.and %v0_7, %v0_10, %v0_4, %v0_13"
                  "    %v0_15 = smt.declare_fun \"ob_501\" : !smt.bool"
                  "    %v0_16 = smt.eq %v0_15, %v0_14 : !smt.bool"
                  "    smt.assert %v0_16"
                  "    %v0_17 = smt.not %v0_15"
                  "    smt.assert %v0_17"
                  "    smt.check sat {} unknown {} unsat {}"
                  "  }"
                  "  // ob_502: fixture obligation"
                  "  // origin: Fixture.clef:1:1"
                  "  smt.solver () : () -> () {"
                  "    smt.set_logic \"QF_LIA\""
                  "    %v0_12 = smt.int.constant 1"
                  "    %v0_13 = smt.int.constant 0"
                  "    %v0_14 = smt.int.cmp ge %v0_12, %v0_13"
                  "    %v0_0 = smt.int.constant 0"
                  "    %v0_1 = smt.int.constant 0"
                  "    %v0_2 = smt.int.cmp ge %v0_0, %v0_1"
                  "    %v0_3 = smt.int.constant 1"
                  "    %v0_4 = smt.int.constant 0"
                  "    %v0_5 = smt.int.cmp gt %v0_3, %v0_4"
                  "    %v0_6 = smt.int.constant 1"
                  "    %v0_7 = smt.int.constant 1"
                  "    %v0_8 = smt.eq %v0_6, %v0_7 : !smt.int"
                  "    %v0_9 = smt.int.constant 1"
                  "    %v0_10 = smt.int.constant 10"
                  "    %v0_11 = smt.int.cmp lt %v0_9, %v0_10"
                  "    %v0_15 = smt.and %v0_14, %v0_2, %v0_5, %v0_8, %v0_11"
                  "    %v0_16 = smt.declare_fun \"ob_502\" : !smt.bool"
                  "    %v0_17 = smt.eq %v0_16, %v0_15 : !smt.bool"
                  "    smt.assert %v0_17"
                  "    %v0_18 = smt.not %v0_16"
                  "    smt.assert %v0_18"
                  "    smt.check sat {} unknown {} unsat {}"
                  "  }"
                  "  // ob_503: fixture obligation"
                  "  // origin: Fixture.clef:1:1"
                  "  smt.solver () : () -> () {"
                  "    smt.set_logic \"QF_LIA\""
                  "    %v0_5 = smt.int.constant 5"
                  "    %v0_6 = smt.int.constant 0"
                  "    %v0_7 = smt.int.cmp ge %v0_5, %v0_6"
                  "    %v0_8 = smt.int.constant 0"
                  "    %v0_9 = smt.eq %v0_8, %v0_8 : !smt.int"
                  "    %v0_10 = smt.int.constant 0"
                  "    %v0_11 = smt.eq %v0_10, %v0_10 : !smt.int"
                  "    %v0_0 = smt.int.constant 6"
                  "    %v0_1 = smt.int.constant 5"
                  "    %v0_2 = smt.int.constant 1"
                  "    %v0_3 = smt.int.add %v0_1, %v0_2"
                  "    %v0_4 = smt.eq %v0_0, %v0_3 : !smt.int"
                  "    %v0_12 = smt.and %v0_7, %v0_9, %v0_11, %v0_4"
                  "    %v0_13 = smt.declare_fun \"ob_503\" : !smt.bool"
                  "    %v0_14 = smt.eq %v0_13, %v0_12 : !smt.bool"
                  "    smt.assert %v0_14"
                  "    %v0_15 = smt.not %v0_13"
                  "    smt.assert %v0_15"
                  "    smt.check sat {} unknown {} unsat {}"
                  "  }"
                  "  // ob_504: fixture obligation"
                  "  // origin: Fixture.clef:1:1"
                  "  smt.solver () : () -> () {"
                  "    smt.set_logic \"QF_LIA\""
                  "    %v0_9 = smt.int.constant 2"
                  "    %v0_10 = smt.int.constant 0"
                  "    %v0_11 = smt.int.cmp ge %v0_9, %v0_10"
                  "    %v0_12 = smt.int.constant 0"
                  "    %v0_13 = smt.eq %v0_12, %v0_12 : !smt.int"
                  "    %v0_14 = smt.int.constant 1"
                  "    %v0_15 = smt.int.constant 0"
                  "    %v0_16 = smt.int.cmp gt %v0_14, %v0_15"
                  "    %v0_0 = smt.int.constant 20"
                  "    %v0_1 = smt.int.constant 2"
                  "    %v0_2 = smt.int.cmp gt %v0_0, %v0_1"
                  "    %v0_3 = smt.int.constant 5"
                  "    %v0_4 = smt.int.constant 2"
                  "    %v0_5 = smt.int.cmp ge %v0_3, %v0_4"
                  "    %v0_6 = smt.int.constant 5"
                  "    %v0_7 = smt.int.constant 20"
                  "    %v0_8 = smt.int.cmp lt %v0_6, %v0_7"
                  "    %v0_17 = smt.and %v0_11, %v0_13, %v0_16, %v0_2, %v0_5, %v0_8"
                  "    %v0_18 = smt.declare_fun \"ob_504\" : !smt.bool"
                  "    %v0_19 = smt.eq %v0_18, %v0_17 : !smt.bool"
                  "    smt.assert %v0_19"
                  "    %v0_20 = smt.not %v0_18"
                  "    smt.assert %v0_20"
                  "    smt.check sat {} unknown {} unsat {}"
                  "  }"
                  "  // ob_505: fixture obligation"
                  "  // origin: Fixture.clef:1:1"
                  "  smt.solver () : () -> () {"
                  "    smt.set_logic \"QF_LIA\""
                  "    %v0_2 = smt.declare_fun \"buffer_absence_accepted_9\" : !smt.bool"
                  "    %v0_0 = smt.declare_fun \"buffer_absence_case\" : !smt.int"
                  "    %v0_1 = smt.declare_fun \"buffer_absence_choice\" : !smt.int"
                  "    %v0_4 = smt.int.constant 1"
                  "    %v0_5 = smt.eq %v0_0, %v0_4 : !smt.int"
                  "    %v0_7 = smt.int.constant 0"
                  "    %v0_8 = smt.eq %v0_0, %v0_7 : !smt.int"
                  "    %v0_10 = smt.eq %v0_1, %v0_7 : !smt.int"
                  "    %v0_12 = smt.not %v0_8"
                  "    %v0_11 = smt.or %v0_12, %v0_10"
                  "    %v0_13 = smt.eq %v0_1, %v0_4 : !smt.int"
                  "    %v0_15 = smt.not %v0_5"
                  "    %v0_14 = smt.or %v0_15, %v0_13"
                  "    %v0_16 = smt.and %v0_5, %v0_2, %v0_11, %v0_14"
                  "    %v0_17 = smt.ite %v0_8, %v0_4, %v0_7 : !smt.int"
                  "    %v0_18 = smt.ite %v0_5, %v0_4, %v0_7 : !smt.int"
                  "    %v0_20 = smt.int.add %v0_17, %v0_18"
                  "    %v0_21 = smt.eq %v0_20, %v0_4 : !smt.int"
                  "    %v0_22 = smt.and %v0_8, %v0_2"
                  "    %v0_23 = smt.ite %v0_22, %v0_7, %v0_4 : !smt.int"
                  "    %v0_24 = smt.eq %v0_1, %v0_23 : !smt.int"
                  "    %v0_25 = smt.and %v0_21, %v0_24"
                  "    smt.assert %v0_16"
                  "    %v0_26 = smt.declare_fun \"ob_505\" : !smt.bool"
                  "    %v0_27 = smt.eq %v0_26, %v0_25 : !smt.bool"
                  "    smt.assert %v0_27"
                  "    %v0_28 = smt.not %v0_26"
                  "    smt.assert %v0_28"
                  "    smt.check sat {} unknown {} unsat {}"
                  "  }"
                  "}" ]
        Assert.Equal(expectedMlir, mlir)

        // ZeroCopyBufferExtent scales MaximumCount by ElementBytes via smt.int.mul.
        let scaledExtentOb =
            obligation (id 507) "foreign-readonly-buffer-extent"
                (ObligationBody.ZeroCopyBufferExtent
                    { Call = id 1; Declaration = id 2; Parameter = 1; CountParameter = 2
                      Buffer = id 3; Count = id 4; MinimumCount = 1I; MaximumCount = 8I; ExtentCapacity = 32I
                      ElementBytes = 4; CountCoverage = id 507 })
        let scaledMlir = Alex.Traversal.SMTTransfer.transfer [ scaledExtentOb ] |> Result.defaultWith failwith
        Assert.Contains("%v0_0 = smt.int.constant 8\n    %v0_1 = smt.int.constant 4\n    %v0_2 = smt.int.mul %v0_0, %v0_1\n    %v0_3 = smt.int.constant 32\n    %v0_4 = smt.int.cmp le %v0_2, %v0_3", scaledMlir)

        // BufferAbsenceArgumentConversion delegates to BufferAbsenceArgumentProof.project for both SourceCase = 0 and SourceCase = 1 and rejects invalid models.
        let noneAbsenceOb =
            obligation (id 508) "foreign-buffer-absence-conversion-0"
                (ObligationBody.BufferAbsenceArgumentConversion
                    { Call = id 1; Parameter = 0; Actual = id 8; Construction = id 8
                      SourceCase = 0; Absence = id 9
                      Arms = [ arm0; arm1 ] })
        let noneAbsenceMlir = Alex.Traversal.SMTTransfer.transfer [ noneAbsenceOb ] |> Result.defaultWith failwith
        Assert.Contains("smt.declare_fun \"buffer_absence_accepted_9\" : !smt.bool", noneAbsenceMlir)
        Assert.Contains("smt.declare_fun \"ob_508\" : !smt.bool", noneAbsenceMlir)

        let corruptOb =
            obligation (id 506) "foreign-buffer-absence-conversion-0"
                (ObligationBody.BufferAbsenceArgumentConversion
                    { Call = id 1; Parameter = 0; Actual = id 8; Construction = id 8
                      SourceCase = 1; Absence = id 9
                      Arms = [ arm0; { arm1 with CaseOrdinal = 9 } ] })
        match Alex.Traversal.SMTTransfer.transfer [ corruptOb ] with
        | Result.Error msg ->
            Assert.Contains("The buffer absence conversion plan requires exact AbsentNull and RequiresNonNullBuffer arms.", msg)
        | Result.Ok _ -> failwith "Admitted corrupt BufferAbsenceArgumentConversion arms"

        let badSourceCaseOb =
            obligation (id 509) "foreign-buffer-absence-conversion-0"
                (ObligationBody.BufferAbsenceArgumentConversion
                    { Call = id 1; Parameter = 0; Actual = id 8; Construction = id 8
                      SourceCase = 2; Absence = id 9
                      Arms = [ arm0; arm1 ] })
        let badSourceCaseMlir = Alex.Traversal.SMTTransfer.transfer [ badSourceCaseOb ] |> Result.defaultWith failwith
        Assert.Contains("smt.int.constant 2", badSourceCaseMlir)

    [<Fact>]
    let ``Boundary buffer calls refuse omitted or reordered actuals before operand traversal`` () =
        // Explicit test fixture: verifies pBoundaryCall enforces complete ordered Parameters vs Arguments for BoundaryBufferCall shapes.
        let baseGraph = explicitZeroCopyFixture true true
        let siteId = id 60
        let baseCall = baseGraph.Emission.Boundary.Calls[siteId]
        let omittedCallGraph =
            { baseGraph with
                Emission =
                    { baseGraph.Emission with
                        Boundary =
                            { baseGraph.Emission.Boundary with
                                Calls = baseGraph.Emission.Boundary.Calls.Add(siteId, { baseCall with Arguments = [ baseCall.Arguments.Head ] }) } } }
        match runBoundaryCallAt siteId omittedCallGraph with
        | Result.Error reason ->
            Assert.Equal("Boundary buffer, borrowed-handle, and borrowed-view calls require their exact direct signature and complete ordered actuals.", reason)
        | Result.Ok other -> failwithf "Admitted omitted ReadOnlyBytes argument: %A" other

        let reorderedCallGraph =
            { baseGraph with
                Emission =
                    { baseGraph.Emission with
                        Boundary =
                            { baseGraph.Emission.Boundary with
                                Calls = baseGraph.Emission.Boundary.Calls.Add(siteId, { baseCall with Arguments = List.rev baseCall.Arguments }) } } }
        match runBoundaryCallAt siteId reorderedCallGraph with
        | Result.Error reason ->
            Assert.Equal("Boundary buffer, borrowed-handle, and borrowed-view calls require their exact direct signature and complete ordered actuals.", reason)
        | Result.Ok other -> failwithf "Admitted reordered BoundaryBufferCall arguments: %A" other

    [<Fact>]
    let ``Resource-bearing Entry callbacks publish ResourceImport cleanly and refuse indirect generic function pointers`` () =
        // Reduced explicit test fixture scoped to ResourceImport publication and indirect generic callback refusal.
        let scopeId = id 700
        let importId = id 701
        let invId = id 702
        let cbFormal = id 703
        let entryFormId = id 704
        let operandId = id 705
        let loadingId = id 706
        let siteId = id 707
        let calleeId = id 708
        let cbArgId = id 0
        let cbInv : BoundaryCallbackInvocation =
            { Identity = invId; Import = importId; Parameter = 0; Formal = cbFormal; Scope = scopeId
              Contract =
                { Binding = "Fixture.cb"; Parameter = 0; Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters = [| { Name = "db"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Void }
                  Hypothesis = { Identity = "fixture.cb.res"; Version = "1"; Source = "component contract" } }
              Signature =
                { CallingConvention = "CDecl"
                  Parameters = [ BoundaryScalar.ResourceHandle(cbFormal, false) ]
                  Result = None }
              Extent = BoundaryCallbackExtent.DuringCall; Participants = Set.singleton invId }
        let fnPtrCHandleType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [ TypeParamKind.Type ]; NativeKind = Some NTUKind.NTUfnptr },
                [ functionFrom ptrHandleType unitType ])
        let cbImport : BoundaryImport =
            { Identity = importId; Binding = scopeId; Scope = scopeId
              Library = "fixture"; Symbol = "fixture_register_cb"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ scopeId ]; Parameters = [ cbFormal, BoundaryScalar.Entry invId ]
              Result = None; Participants = Set.ofList [ scopeId; importId; invId; cbFormal ]
              SourceTypes = Map.ofList [ cbFormal, fnPtrCHandleType ]
              DeclarationFacts = Map.ofList [ cbFormal, { emptyFact "binding" with SourceType = fnPtrCHandleType } ] }
        let contract : BAREWire.Platform.ProcessLinkContract =
            { Identity = "fixture-process-link"; Version = "1"; Source = "fixture-explicit-assumption"
              Library = "fixture"; Runtime = "libc"; Os = "linux"; Arch = "x86_64"
              LoadAt = "ProcessStartup"; LiveUntil = "ProcessTermination"
              Unloading = "Forbidden"; ExportedLibrary = "Forbidden" }
        let loading : BoundaryLoading =
            { Identity = loadingId; Binding = scopeId; Selector = "fixture.loading"
              Contract = contract; Platform = id 710; Core = id 711
              DeclarationFacts = Map.empty; Participants = Set.ofList [ loadingId; scopeId; id 710; id 711 ] }
        let fnType = functionFrom ptrHandleType unitType
        let entryRow : BoundaryEntry =
            { Formation = entryFormId; Operand = operandId; Import = importId; Declaration = scopeId
              Loading = loadingId; SourceType = fnType; Transport = Set.singleton calleeId
              Participants = Set.ofList [ entryFormId; operandId; importId; scopeId; loadingId; calleeId ] }
        let callRow : BoundaryCall =
            { Site = siteId; Import = importId; Callee = calleeId; Entry = Some entryFormId; Resource = None
              Arguments = [ { Actual = cbArgId; Formal = cbFormal; Abi = BoundaryScalar.Entry invId; Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = None; ResultAdaptation = None
              Participants = Set.ofList [ siteId; importId; calleeId; entryFormId; cbArgId; cbFormal; invId ]; SourceTypes = Map.empty }
        let emptyGraph = revision []
        let boundary =
            { emptyGraph.Emission.Boundary with
                Loading = Some loading
                Imports = Map.ofList [ importId, cbImport ]
                ByScope = Map.ofList [ scopeId, [ importId ] ]
                CallbackInvocations = Map.ofList [ invId, cbInv ]
                Entries = Map.ofList [ entryFormId, entryRow ]
                Calls = Map.ofList [ siteId, callRow ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId boundary with
        | Result.Ok [ MLIROp.ResourceImport imp ] ->
            Assert.Equal(importId, imp.Identity)
            Assert.Equal(Result.Ok NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [ MLIROp.ResourceImport imp ])
        | other -> failwithf "Unexpected boundaryImportsAt result for callback-nested ResourceHandle: %A" other

        let graph =
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ entryFormId, mkNode entryFormId fnType (SemanticKind.Application(id 709, [ operandId ])) [ operandId ]
                          operandId, mkNode operandId fnType (SemanticKind.VarRef("fixture_register_cb", Some scopeId)) []
                          siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ cbArgId ])) [ calleeId; cbArgId ]
                          calleeId, mkNode calleeId fnType (SemanticKind.VarRef("fptr", None)) []
                          cbArgId, mkNode cbArgId fnType (SemanticKind.VarRef("cb", None)) [] ]
                Emission =
                    { emptyGraph.Emission with
                        Boundary = boundary
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ] } } }
            |> declareTraversalReadings

        let accAddr = MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.PlatformPatterns.pImportedFunctionAddress entryFormId) (focus graph graph.Nodes[entryFormId]) 64 accAddr with
        | Result.Error reason ->
            Assert.Equal("Resource-bearing imports require a direct source call, not a generic function pointer.", reason)
            Assert.Empty accAddr.AllOps
            Assert.True((MLIRAccumulator.recallNode entryFormId accAddr).IsNone)
        | Result.Ok other -> failwithf "Admitted pImportedFunctionAddress for callback-nested ResourceHandle: %A" other

        let accCall = MLIRAccumulator.empty ()
        MLIRAccumulator.bindNode cbArgId (Arg 0) (TFunc([ TOpaqueHandle(ptrHandleType, 64, 8) ], [])) accCall
        match matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus graph graph.Nodes[siteId]) 64 accCall with
        | Result.Error reason ->
            Assert.Equal("Resource-bearing imports require a direct source call, not a generic function pointer.", reason)
            Assert.Empty accCall.AllOps
            Assert.True((MLIRAccumulator.recallNode siteId accCall).IsNone)
        | Result.Ok other -> failwithf "Admitted indirect pBoundaryCall for callback-nested ResourceHandle: %A" other

    [<Fact>]
    let ``callbackHandleRepAt allows at most one settled optional wrapper and rejects double wrapping`` () =
        // Explicit test fixture: verifies callbackHandleRepAt settles Option<FnPtr<_>> and rejects Wrapper<Option<FnPtr<_>>>.
        let importId = id 750
        let cbFormal = id 751
        let fnPtrType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [ TypeParamKind.Type ]; NativeKind = Some NTUKind.NTUfnptr },
                [ functionFrom ptrHandleType unitType ])
        let optFnType = optionOf fnPtrType
        let doubleWrappedType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "Wrapper" }; Parameters = [ TypeParamKind.Type ]; NativeKind = None },
                [ optFnType ])
        let optFnRep = ValueRepresentation.Union([ "None", []; "Some", [ ValueRepresentation.Scalar(SettledSlot.Pointer 1) ] ], Some(1, 16, 8))
        let baseImport : BoundaryImport =
            { Identity = importId; Binding = id 752; Scope = id 752
              Library = "fixture"; Symbol = "fixture_opt_cb"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ id 752 ]; Parameters = [ cbFormal, BoundaryScalar.Entry (id 753) ]
              Result = None; Participants = Set.singleton cbFormal
              SourceTypes = Map.ofList [ cbFormal, optFnType ]
              DeclarationFacts = Map.ofList [ cbFormal, { emptyFact "binding" with SourceType = optFnType } ] }
        let emptyGraph = revision []
        let graphWithType ty =
            { emptyGraph with
                Emission =
                    { emptyGraph.Emission with
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations =
                                    Map.ofList
                                        [ ty, Result.Ok optFnRep
                                          ptrHandleType, Result.Ok handleRep ] } } }
        match BoundaryAbi.callbackHandleRepAt (graphWithType optFnType) baseImport cbFormal 0 false with
        | Some rep -> Assert.Equal(handleRep, rep)
        | None -> failwith "Expected callbackHandleRepAt to admit single settled optional wrapper around FnPtr"

        let doubleImport =
            { baseImport with
                SourceTypes = Map.ofList [ cbFormal, doubleWrappedType ]
                DeclarationFacts = Map.ofList [ cbFormal, { emptyFact "binding" with SourceType = doubleWrappedType } ] }
        Assert.True((BoundaryAbi.callbackHandleRepAt (graphWithType doubleWrappedType) doubleImport cbFormal 0 false).IsNone)

    [<Fact>]
    let ``Closed native callbacks with ResourceHandle and ReadOnlyBytes parameters witness LambdaWitness and pClosedFunctionAddress cleanly`` () =
        // Explicit test fixture: verifies LambdaWitness and pClosedFunctionAddress resolve ResourceHandle + ReadOnlyBytes
        // callback parameters without throwing ArgumentException, and return clean errors on withdrawn representations.
        let countedId = id 800
        let invId = id 801
        let importId = id 802
        let entryId = id 803
        let ctxFormal = id 804
        let argcFormal = id 805
        let argvFormal = id 806
        let implId = id 807
        let bodyId = id 808
        let cbFormal = id 809
        let fnPtrCHandleType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [ TypeParamKind.Type ]; NativeKind = Some NTUKind.NTUfnptr },
                [ TypeIdentity.Function(TypeIdentity.Tuple(false, [ ptrHandleType; intType; uint8Type ]), unitType) ])
        let countedRow : BoundaryCountedEntryArray =
            { Identity = countedId; Import = importId; Parameter = 0; Invocation = invId
              Contract =
                { Binding = "Fixture.xFunc"; Parameter = 5; Argument = 2; CountArgument = 1
                  Element = BAREWire.Descriptors.CountedElement.Handle "sqlite3_value*" }
              DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let invocation : BoundaryCallbackInvocation =
            { Identity = invId; Import = importId; Parameter = 5; Formal = cbFormal; Scope = id 810
              Contract =
                { Binding = "Fixture.createFn"; Parameter = 5; Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters =
                        [| { Name = "ctx"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Void }
                  Hypothesis = { Identity = "fixture.retcb"; Version = "1"; Source = "component contract" } }
              Signature =
                { CallingConvention = "CDecl"
                  Parameters =
                    [ BoundaryScalar.ResourceHandle(cbFormal, false)
                      BoundaryScalar.Integer(32, true)
                      BoundaryScalar.ReadOnlyBytes countedId ]
                  Result = None }
              Extent = BoundaryCallbackExtent.DuringCall
              Participants = Set.singleton invId }
        let cbImport : BoundaryImport =
            { Identity = importId; Binding = id 811; Scope = id 811
              Library = "fixture"; Symbol = "fixture_create_fn"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ id 811 ]; Parameters = [ cbFormal, BoundaryScalar.Entry invId ]
              Result = None; Participants = Set.ofList [ importId; cbFormal; invId ]
              SourceTypes = Map.ofList [ cbFormal, fnPtrCHandleType ]
              DeclarationFacts = Map.ofList [ cbFormal, { emptyFact "binding" with Text = [ "xFunc" ]; SourceType = fnPtrCHandleType } ] }
        let closedEntry : BoundaryClosedEntry =
            { Formation = entryId; Operand = id 812; Declaration = id 811; Implementation = implId
              Formals = [ ctxFormal; argcFormal; argvFormal ]; Body = bodyId
              Lifetime = { Module = id 811; Binding = id 811; Implementation = implId }
              Invocation = invId; ParameterAdaptations = [ None; None; None ]; ResultAdaptation = None
              Registrations = Map.empty; Transport = Set.singleton entryId; Participants = Set.singleton entryId }
        let decl : CallableEmissionDeclaration =
            { Lookup = implId; Implementation = implId
              Parameters = [ "ctx", ptrHandleType, ctxFormal; "argc", intType, argcFormal; "argv", uint8Type, argvFormal ]
              Result = bodyId; Context = LambdaContext.RegularClosure; Captures = []
              Name = CallableSymbolName.ModuleBinding("Fixture", "xFunc"); Parent = None; Participants = Set.empty }
        let dummyFnType = TypeIdentity.Function(ptrHandleType, unitType)
        let emptyGraph = revision []
        let mkGraph (withHandleRep: bool) =
            let occReps =
                if withHandleRep then
                    Map.ofList
                        [ ctxFormal, Result.Ok handleRep
                          bodyId, Result.Ok(ValueRepresentation.Scalar SettledSlot.Unit) ]
                else
                    Map.ofList [ bodyId, Result.Ok(ValueRepresentation.Scalar SettledSlot.Unit) ]
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ entryId, mkNode entryId dummyFnType (SemanticKind.VarRef("xFunc_entry", Some implId)) []
                          implId, mkNode implId dummyFnType (SemanticKind.Lambda(decl.Parameters, bodyId, [], None, LambdaContext.RegularClosure)) [ bodyId ]
                          ctxFormal, mkNode ctxFormal ptrHandleType (SemanticKind.PatternBinding "ctx") []
                          argcFormal, mkNode argcFormal intType (SemanticKind.PatternBinding "argc") []
                          argvFormal, mkNode argvFormal uint8Type (SemanticKind.PatternBinding "argv") []
                          bodyId, mkNode bodyId unitType (SemanticKind.VarRef("unitBody", None)) [] ]
                Emission =
                    { emptyGraph.Emission with
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ importId, cbImport ]
                                CountedEntryArrays = Map.ofList [ countedId, countedRow ]
                                CallbackInvocations = Map.ofList [ invId, invocation ]
                                ClosedEntries = Map.ofList [ entryId, closedEntry ] }
                        Callable =
                            { emptyGraph.Emission.Callable with
                                Declarations = Map.ofList [ implId, decl ]
                                NativeEntries = Map.ofList [ implId, "xFunc_native" ]
                                UnitNodes = Set.singleton bodyId
                                ValueShapes = Map.ofList [ ctxFormal, CallableValueShape.Data ctxFormal ]
                                AliasTargets = Map.ofList [ entryId, entryId; implId, implId; bodyId, bodyId ]
                                Supports = Map.ofList [ entryId, Set.singleton entryId; implId, Set.singleton implId; bodyId, Set.singleton bodyId ]
                                ClosedData = Set.singleton ctxFormal }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations = occReps } } }
            |> declareTraversalReadings

        let expectedParamTypes =
            [ TOpaqueHandle(ptrHandleType, 64, 8)
              TInt(IntWidth 32)
              TMemRef(TInt(IntWidth 8)) ]
        let expectedFnType = TFunc(expectedParamTypes, [])
        let goodGraph = mkGraph true
        let accAddr = MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.FunctionPointerPatterns.pClosedFunctionAddress entryId "xFunc_native" implId) (focus goodGraph goodGraph.Nodes[entryId]) 64 accAddr with
        | Result.Ok(([ MLIROp.FuncOp(FuncOp.FuncConstant(_, "xFunc_native", ty)) ], TRValue v), _) ->
            Assert.Equal(expectedFnType, ty)
            Assert.Equal(expectedFnType, v.Type)
        | other -> failwithf "Unexpected pClosedFunctionAddress result for ResourceHandle/ReadOnlyBytes callback: %A" other

        let badGraph = mkGraph false
        let accBadAddr = MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.FunctionPointerPatterns.pClosedFunctionAddress entryId "xFunc_native" implId) (focus badGraph badGraph.Nodes[entryId]) 64 accBadAddr with
        | Result.Error reason ->
            Assert.Equal("Callable signature data participant 804 lacks its source-published physical representation.", reason)
            Assert.Empty accBadAddr.AllOps
            Assert.True((MLIRAccumulator.recallNode entryId accBadAddr).IsNone)
        | Result.Ok other -> failwithf "Admitted pClosedFunctionAddress with missing ctxFormal representation: %A" other

        let runLambda (g: Revision) =
            let acc = MLIRAccumulator.empty ()
            let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
            let visited = ref Set.empty
            acc.WitnessScope <- Some(Alex.Correspondence.beginWholeGraphWitness g)
            let ctx : WitnessContext =
                { Coeffects = coeffects 64; Accumulator = acc; RootAccumulator = acc
                  ScopeContext = scope; RootScopeContext = scope; Graph = g
                  Zipper = focus g g.Nodes[implId]; GlobalVisited = visited; TraversalVisited = visited }
            let bodyCombinator (_: WitnessContext) (n: SemanticNode) =
                if n.Id = bodyId then { WitnessOutput.empty with Result = TRVoid }
                else WitnessOutput.empty
            let output = (Alex.Witnesses.LambdaWitness.createNanopass (fun () -> bodyCombinator)).Witness ctx g.Nodes[implId]
            output, Alex.Traversal.ScopeContext.ScopeContext.getOps scope.Value, acc

        let goodLambda, goodOps, _ = runLambda goodGraph
        match goodLambda.Result, goodOps with
        | TRVoid, [ MLIROp.FuncOp(FuncOp.FuncDef("xFunc_native", paramPairs, [], _, _)) ] ->
            Assert.Equal<MLIRType list>(expectedParamTypes, List.map snd paramPairs)
        | other -> failwithf "Unexpected LambdaWitness result for ResourceHandle/ReadOnlyBytes callback: %A" other

        let badLambda, badOps, badAcc = runLambda badGraph
        match badLambda.Result with
        | TRError diag ->
            Assert.Equal("Callable formal components: Callable signature data participant 804 lacks its source-published physical representation.", diag.Message)
            Assert.Empty badOps
            Assert.True((MLIRAccumulator.recallNode implId badAcc).IsNone)
        | other -> failwithf "Admitted LambdaWitness with missing ctxFormal representation: %A" other

        // F2: invalid/unsupported ValueRepresentation flows through TypeMapping.tryValueTypeAt without exception
        let badRepGraph =
            { goodGraph with
                Emission =
                    { goodGraph.Emission with
                        Numeric =
                            { goodGraph.Emission.Numeric with
                                OccurrenceRepresentations =
                                    Map.add ctxFormal (Result.Ok(ValueRepresentation.Tag 0)) goodGraph.Emission.Numeric.OccurrenceRepresentations } } }
        let accBadRepAddr = MLIRAccumulator.empty ()
        match matchAt (Alex.Patterns.FunctionPointerPatterns.pClosedFunctionAddress entryId "xFunc_native" implId) (focus badRepGraph badRepGraph.Nodes[entryId]) 64 accBadRepAddr with
        | Result.Error reason ->
            Assert.Equal("TypeMapping: source tag has no cases", reason)
            Assert.Empty accBadRepAddr.AllOps
            Assert.True((MLIRAccumulator.recallNode entryId accBadRepAddr).IsNone)
        | Result.Ok other -> failwithf "Admitted pClosedFunctionAddress with invalid ValueRepresentation: %A" other
        let badRepLambda, badRepOps, badRepAcc = runLambda badRepGraph
        match badRepLambda.Result with
        | TRError diag ->
            Assert.Equal("Callable formal components: TypeMapping: source tag has no cases", diag.Message)
            Assert.Empty badRepOps
            Assert.True((MLIRAccumulator.recallNode implId badRepAcc).IsNone)
        | other -> failwithf "Admitted LambdaWitness with invalid ValueRepresentation: %A" other

    [<Fact>]
    let ``StaticImageNulBorrowed refuses missing StaticStringPool entry, omitted origin NodeId, and mismatched UncountedPathTermination`` () =
        let roId = id 1150
        let declBinding = id 1151
        let bodyId = id 1152
        let descId = id 1153
        let bufFormal = id 1154
        let siteId = id 1160
        let calleeId = id 1161
        let bufActual = id 0
        let termClaimId = id 1163
        let retClaimId = id 1164
        let resId = id 1165
        let support = Set.ofList [ roId; declBinding; bodyId; descId; bufFormal; siteId; calleeId; bufActual; termClaimId; retClaimId; resId ]
        let descFacts =
            let pCase = id 1950
            let arrId = id 1951
            Map.ofList
                [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                  bufFormal, { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
                  arrId, { emptyFact "array" with References = [ bufFormal ]; Children = [ bufFormal ] }
                  descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let roDecl : BoundaryReadOnlyBufferDeclaration =
            { Identity = roId; Declaration = declBinding; Body = bodyId; Formals = [ bufFormal ]; Descriptor = descId
              Parameter = 0; CountParameter = None; BufferFormal = bufFormal; CountFormal = None
              Contract =
                { Binding = "Fixture.puts"; Parameter = 0
                  Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                  Hypothesis = { Identity = "fixture.puts"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let roUse : BoundaryReadOnlyBufferUse =
            { Call = siteId; Declaration = roId; Parameter = 0; Buffer = bufActual; Residence = resId
              Retirements = []; Copies = 0
              Crossing = BoundaryReadOnlyBufferCrossing.StaticImageNulBorrowed(0, bufActual, 2I, termClaimId)
              RetentionProof = retClaimId; AccessExclusivityProof = None; Participants = ParticipantEvidence.Established [] }
        let mkTermOb (trailingNul: bool) =
            obligation termClaimId "foreign-uncounted-path-termination"
                (ObligationBody.UncountedPathTermination
                    { Call = siteId; Declaration = roId; Parameter = 0; Source = bufActual; ByteLength = 2I
                      Mode = UncountedPathStagingMode.StaticImageZeroCopy 0
                      RequiresNoInteriorNul = true; RequiresTrailingNul = trailingNul })
        let retOb =
            obligation retClaimId "foreign-buffer-retention-domination"
                (ObligationBody.BufferRetentionDomination
                    { Call = siteId; Declaration = roId; Buffer = bufActual; Residence = resId
                      Mode = BufferRetentionMode.DuringCall; AcquireOrder = 1; RetirementOrders = [] })
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding
              Library = "fixture"; Symbol = "fixture_puts"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]; Parameters = [ bufFormal, BoundaryScalar.ReadOnlyBytes roId ]
              Result = None; Participants = support; SourceTypes = Map.empty; DeclarationFacts = descFacts }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments = [ { Actual = bufActual; Formal = bufFormal; Abi = BoundaryScalar.ReadOnlyBytes roId; Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = None; ResultAdaptation = None; Participants = support; SourceTypes = Map.empty }
        let emptyGraph = revision []
        let mkStatic (entries: StaticStringEntry list) (trailingNul: bool) =
            let termOb = mkTermOb trailingNul
            { emptyGraph with
                StaticStringPool =
                    Some
                        { Symbol = ".rodata.str"; Bytes = [ 104uy; 105uy; 0uy ]; Alignment = 1; Size = 3; UsedSize = 3
                          Entries = entries
                          SpaceName = "rodata"; Capacity = 16L; SpaceAlignment = 1; Granularity = 1; DeclarationNode = declBinding }
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ bufActual ])) [ calleeId; bufActual ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_puts", Some declBinding)) []
                          bufActual, mkNode bufActual unitType (SemanticKind.VarRef("s", None)) []
                          termClaimId, mkNode termClaimId unitType (SemanticKind.Obligation termOb) []
                          retClaimId, mkNode retClaimId unitType (SemanticKind.Obligation retOb) [] ]
                Obligations = [ termOb; retOb ]
                Emission =
                    { emptyGraph.Emission with
                        Numeric = { emptyGraph.Emission.Numeric with OccurrenceRepresentations = Map.ofList [ bufActual, Result.Ok bufRep ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow ]
                                Calls = Map.ofList [ siteId, callRow ]
                                ReadOnlyBufferDeclarations = Map.ofList [ roId, roDecl ]
                                ReadOnlyBufferUses = Map.ofList [ (siteId, 0), roUse ] } } }
        let validEntry : StaticStringEntry = { Content = "hi"; Offset = 0; Length = 2; StorageLength = 3; NodeIds = [ bufActual ] }
        let missingOriginEntry : StaticStringEntry = { validEntry with NodeIds = [ id 999 ] }
        for badGraph in [ mkStatic [] true; mkStatic [ missingOriginEntry ] true; mkStatic [ validEntry ] false ] do
            match runBoundaryCallAt siteId badGraph with
            | Result.Error reason ->
                Assert.Equal("Read-only buffer argument at boundary call 1160 operand 0 lacks its exact source crossing, extent/termination, or retention account.", reason)
            | Result.Ok other -> failwithf "Admitted defective StaticImageNulBorrowed: %A" other

    [<Fact>]
    let ``BorrowedResultView refuses malformed companion import, companion entry, and mismatched companion actual`` () =
        let bvId = id 1350
        let declBinding = id 1351
        let bodyId = id 1352
        let descId = id 1353
        let ownerFormal = id 1354
        let siteId = id 1360
        let calleeId = id 1361
        let ownerActual = id 0
        let wrongActual = id 1399
        let invId = id 1362
        let readId = id 1363
        let scopeClaimId = id 1364
        let compSiteId = id 1365
        let compImportId = id 1366
        let support = Set.ofList [ bvId; declBinding; bodyId; descId; ownerFormal; siteId; calleeId; ownerActual; invId; readId; scopeClaimId; compSiteId; compImportId ]
        let descFacts =
            let pCase = id 1980
            let arrId = id 1981
            Map.ofList
                [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                  ownerFormal, { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
                  arrId, { emptyFact "array" with References = [ ownerFormal ]; Children = [ ownerFormal ] }
                  descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let bvDecl : BoundaryBorrowedResultViewDeclaration =
            { Identity = bvId; Declaration = declBinding; Body = bodyId; Formals = [ ownerFormal ]; Descriptor = descId
              OwnerParameter = 0; OwnerFormal = ownerFormal
              Contract =
                { Binding = "Fixture.columnText"; Owner = 0
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Extent = BAREWire.Descriptors.BorrowedExtent.CompanionCall("Fixture.columnBytes", [| 0 |])
                  InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.OwnerCall { Binding = "Fixture.step"; Parameter = 0 } |]
                  Hypothesis = { Identity = "fixture.bv"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let bvUse : BoundaryBorrowedResultViewUse =
            { Call = siteId; Declaration = bvId; Owner = ownerActual; View = siteId
              CompanionCall = Some compSiteId; CompanionArguments = [ ownerActual ]
              CallOrder = 10; Invalidations = [ invId ]; InvalidationOrders = [ 20 ]
              Reads = [ readId ]; ReadOrders = [ 12 ]; NullToNoneBoundary = true
              ScopeProof = scopeClaimId; Participants = ParticipantEvidence.Established [] }
        let scopeOb =
            obligation scopeClaimId "foreign-borrowed-view-scope"
                (ObligationBody.BorrowedResultViewScope
                    { Call = siteId; Declaration = bvId; Owner = ownerActual; View = siteId
                      CallOrder = 10; InvalidationOrders = [ 20 ]; ReadOrders = [ 12 ]
                      NullToNoneBoundary = true })
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding
              Library = "fixture"; Symbol = "fixture_column_text"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]; Parameters = [ ownerFormal, BoundaryScalar.ResourceHandle(ownerFormal, false) ]
              Result = Some(BoundaryScalar.BorrowedBytes bvId); Participants = support
              SourceTypes = Map.ofList [ ownerFormal, ptrHandleType ]
              DeclarationFacts = descFacts.Add(ownerFormal, { descFacts[ownerFormal] with SourceType = ptrHandleType }) }
        let compImport : BoundaryImport =
            { Identity = compImportId; Binding = id 1367; Scope = id 1367
              Library = "fixture"; Symbol = "fixture_column_bytes"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ id 1367 ]; Parameters = [ ownerFormal, BoundaryScalar.ResourceHandle(ownerFormal, false) ]
              Result = Some(BoundaryScalar.Integer(32, true)); Participants = Set.empty; SourceTypes = Map.empty; DeclarationFacts = Map.empty }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments = [ { Actual = ownerActual; Formal = ownerFormal; Abi = BoundaryScalar.ResourceHandle(ownerFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.BorrowedBytes bvId); ResultAdaptation = None
              Participants = support; SourceTypes = Map.empty }
        let compCall : BoundaryCall =
            { Site = compSiteId; Import = compImportId; Callee = id 1368; Entry = None; Resource = None
              Arguments = [ { Actual = ownerActual; Formal = ownerFormal; Abi = BoundaryScalar.ResourceHandle(ownerFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.Integer(32, true)); ResultAdaptation = None
              Participants = Set.empty; SourceTypes = Map.empty }
        let emptyGraph = revision []
        let mkGraph (badCompImport: BoundaryImport) (badCompCall: BoundaryCall) =
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ ownerActual ])) [ calleeId; ownerActual ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_column_text", Some declBinding)) []
                          ownerActual, mkNode ownerActual ptrHandleType (SemanticKind.VarRef("stmt", None)) []
                          scopeClaimId, mkNode scopeClaimId unitType (SemanticKind.Obligation scopeOb) [] ]
                Obligations = [ scopeOb ]
                Emission =
                    { emptyGraph.Emission with
                        Callable = { emptyGraph.Emission.Callable with AliasTargets = Map.ofList [ siteId, siteId ] }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ ownerActual, Result.Ok handleRep
                                          ownerFormal, Result.Ok handleRep
                                          siteId, Result.Ok bufRep ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow; compImportId, badCompImport ]
                                Calls = Map.ofList [ siteId, callRow; compSiteId, badCompCall ]
                                BorrowedResultViewDeclarations = Map.ofList [ bvId, bvDecl ]
                                BorrowedResultViewUses = Map.ofList [ siteId, bvUse ] } } }
        let badGraphs =
            [ mkGraph { compImport with Result = None } { compCall with Result = None }
              mkGraph compImport { compCall with Entry = Some(id 1398) }
              mkGraph compImport { compCall with Arguments = [ { compCall.Arguments.Head with Actual = wrongActual } ] } ]
        for badGraph in badGraphs do
            match runBoundaryCallAt siteId badGraph with
            | Result.Error reason ->
                Assert.Equal("Borrowed result view at boundary call 1360 lacks its exact non-owning declaration, invalidation frontier, or scope claim.", reason)
            | Result.Ok other -> failwithf "Admitted malformed CompanionCall in BorrowedResultView: %A" other

    [<Fact>]
    let ``CountedEntryArrays direct call parameters enforce invocation, ordinal, and formal count`` () =
        let importId = id 1450
        let countedId = id 1451
        let invId = id 1452
        let wrongInvId = id 1459
        let entryId = id 1453
        let implId = id 1454
        let ctxFormal = id 1455
        let argcFormal = id 1456
        let argvFormal = id 1457
        let bodyId = id 1458
        let siteId = id 1460
        let contract : BAREWire.Descriptors.CountedEntryArrayDescriptor =
            { Binding = "Fixture.xFunc"; Parameter = 5; Argument = 2; CountArgument = 1
              Element = BAREWire.Descriptors.CountedElement.Handle "sqlite3_value*" }
        let countedRow : BoundaryCountedEntryArray =
            { Identity = countedId; Import = importId; Parameter = 0; Invocation = invId
              Contract = contract; DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let cbFormal = id 1461
        let fnPtrCHandleType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "FnPtr" }; Parameters = [ TypeParamKind.Type ]; NativeKind = Some NTUKind.NTUfnptr },
                [ TypeIdentity.Function(TypeIdentity.Tuple(false, [ ptrHandleType; intType; uint8Type ]), unitType) ])
        let cbInv : BoundaryCallbackInvocation =
            { Identity = invId; Import = importId; Parameter = 0; Formal = cbFormal; Scope = id 1462
              Contract =
                { Binding = "Fixture.cb"; Parameter = 0; Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters =
                        [| { Name = "ctx"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Void }
                  Hypothesis = { Identity = "fixture.cb"; Version = "1"; Source = "component contract" } }
              Signature =
                { CallingConvention = "CDecl"
                  Parameters = [ BoundaryScalar.ResourceHandle(cbFormal, false); BoundaryScalar.Integer(32, true); BoundaryScalar.ReadOnlyBytes countedId ]
                  Result = None }
              Extent = BoundaryCallbackExtent.DuringCall; Participants = Set.singleton invId }
        let cbImport : BoundaryImport =
            { Identity = importId; Binding = id 1462; Scope = id 1462; Library = "fixture"; Symbol = "fixture_exec"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ id 1462 ]; Parameters = [ cbFormal, BoundaryScalar.Entry invId ]; Result = None
              Participants = Set.ofList [ importId; cbFormal; invId ]
              SourceTypes = Map.ofList [ cbFormal, fnPtrCHandleType ]
              DeclarationFacts = Map.ofList [ cbFormal, { emptyFact "binding" with Text = [ "xFunc" ]; SourceType = fnPtrCHandleType } ] }
        let entry : BoundaryClosedEntry =
            { Formation = entryId; Operand = id 1463; Declaration = id 1462; Implementation = implId
              Formals = [ ctxFormal; argcFormal; argvFormal ]; Body = bodyId
              Lifetime = { Module = id 1462; Binding = id 1462; Implementation = implId }
              Invocation = invId; ParameterAdaptations = [ None; None; None ]; ResultAdaptation = None
              Registrations = Map.empty; Transport = Set.singleton entryId; Participants = Set.singleton entryId }
        let decl : CallableEmissionDeclaration =
            { Lookup = implId; Implementation = implId
              Parameters = [ "ctx", ptrHandleType, ctxFormal; "argc", intType, argcFormal; "argv", uint8Type, argvFormal ]
              Result = bodyId; Context = LambdaContext.RegularClosure; Captures = []
              Name = CallableSymbolName.ModuleBinding("Fixture", "xFunc"); Parent = None; Participants = Set.empty }
        let directCallProof : CallableEmissionCall =
            { Site = siteId; Implementation = implId; Parameters = decl.Parameters
              Arguments = [ ctxFormal; argcFormal; argvFormal ]; Result = bodyId
              SignatureData = Set.empty; Participants = Set.empty }
        let emptyGraph = revision []
        let mkBadGraph (badCounted: BoundaryCountedEntryArray) (badSigParams: BoundaryScalar list) =
            let badInv = { cbInv with Signature = { cbInv.Signature with Parameters = badSigParams } }
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(implId, [ ctxFormal; argcFormal; argvFormal ])) [ implId; ctxFormal; argcFormal; argvFormal ]
                          implId, mkNode implId (TypeIdentity.Function(ptrHandleType, unitType)) (SemanticKind.Lambda([ "ctx", ptrHandleType, ctxFormal ], bodyId, [], None, LambdaContext.RegularClosure)) [ bodyId ]
                          ctxFormal, mkNode ctxFormal ptrHandleType (SemanticKind.PatternBinding "ctx") []
                          argcFormal, mkNode argcFormal intType (SemanticKind.PatternBinding "argc") []
                          argvFormal, mkNode argvFormal uint8Type (SemanticKind.PatternBinding "argv") []
                          bodyId, mkNode bodyId unitType (SemanticKind.VarRef("unitBody", None)) [] ]
                Emission =
                    { emptyGraph.Emission with
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ importId, cbImport ]
                                CountedEntryArrays = Map.ofList [ countedId, badCounted ]
                                CallbackInvocations = Map.ofList [ invId, badInv ]
                                ClosedEntries = Map.ofList [ entryId, entry ] }
                        Callable =
                            { emptyGraph.Emission.Callable with
                                Declarations = Map.ofList [ implId, decl ]
                                NativeEntries = Map.ofList [ implId, "xFunc_native" ]
                                UnitNodes = Set.singleton bodyId
                                Calls = Map.ofList [ siteId, directCallProof ]
                                ValueShapes = Map.ofList [ ctxFormal, CallableValueShape.Data ctxFormal ]
                                ClosedData = Set.singleton ctxFormal }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ ctxFormal, Result.Ok handleRep
                                          bodyId, Result.Ok(ValueRepresentation.Scalar SettledSlot.Unit) ] } } }
            |> declareTraversalReadings
        let checkFailure (g: Revision) (expected: string) =
            let acc = MLIRAccumulator.empty ()
            let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
            let visited = ref Set.empty
            let ctx : WitnessContext =
                { Coeffects = coeffects 64; Accumulator = acc; RootAccumulator = acc
                  ScopeContext = scope; RootScopeContext = scope; Graph = g
                  Zipper = focus g g.Nodes[siteId]; GlobalVisited = visited; TraversalVisited = visited }
            match Alex.Traversal.CallableOperands.parametersAtCall ctx siteId implId decl.Parameters with
            | Result.Error reason ->
                Assert.Equal(expected, reason)
                Assert.Empty acc.AllOps
                Assert.True((MLIRAccumulator.recallNode siteId acc).IsNone)
            | Result.Ok other -> failwithf "Admitted defective CountedEntryArrays direct call: %A" other
        checkFailure (mkBadGraph { countedRow with Invocation = wrongInvId } cbInv.Signature.Parameters) "Closed native counted-entry array differs from its receiving invocation or parameter ordinal."
        checkFailure (mkBadGraph { countedRow with Contract = { contract with Argument = 1 } } cbInv.Signature.Parameters) "Closed native counted-entry array differs from its receiving invocation or parameter ordinal."
        checkFailure (mkBadGraph countedRow (List.take 2 cbInv.Signature.Parameters)) "Closed native direct call omitted or reordered an original formal."

    [<Fact>]
    let ``pResourceCall AcquireNullable and direct pBoundaryCall refuse mismatched parameters and indirect entry`` () =
        let resId = id 1500
        let acqBinding = id 1501
        let relBinding = id 1502
        let acqDescId = id 1503
        let relDescId = id 1504
        let acqFormal = id 1505
        let relFormal = id 1506
        let acqSiteId = id 1507
        let acqCalleeId = id 1508
        let acqActual = id 0
        let cleanupId = id 1509
        let optHandleType = optionOf ptrHandleType
        let optHandleRep =
            ValueRepresentation.Union(
                [ "None", []; "Some", [ ValueRepresentation.Scalar(SettledSlot.CHandle(ptrHandleType, 64, 8)) ] ],
                Some(0, 16, 8))
        let resDecl : BoundaryResourceDeclaration =
            { Identity = resId; Acquisition = acqBinding; AcquisitionBody = id 1510; AcquisitionDescriptor = acqDescId
              Release = relBinding; ReleaseBody = id 1511; ReleaseDescriptor = relDescId; ReleaseFormal = relFormal; ReleaseOrdinal = 0
              PointerBits = 64; AcquisitionType = intType; ResultType = optHandleType; HandleType = ptrHandleType
              Contract =
                { Resource = BAREWire.Descriptors.ResourceProtocol.OwnedNullableReturn { Binding = "Fixture.close"; Parameter = 0 }
                  Hypothesis = { Identity = "fixture.res"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = Map.empty; Participants = Set.singleton resId }
        let acqImport : BoundaryImport =
            { Identity = acqDescId; Binding = acqBinding; Scope = acqBinding
              Library = "fixture"; Symbol = "fixture_open"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ acqBinding ]; Parameters = [ acqFormal, BoundaryScalar.Integer(32, true) ]
              Result = Some(BoundaryScalar.ResourceHandle(resId, true)); Participants = Set.empty; SourceTypes = Map.empty; DeclarationFacts = Map.empty }
        let acqCall : BoundaryCall =
            { Site = acqSiteId; Import = acqDescId; Callee = acqCalleeId; Entry = None
              Resource =
                Some(
                    BoundaryResourceUse.AcquireNullable
                        { Declaration = resId; Tag = SettledSlot.Integer(8, None)
                          NoneCase = 0; SomeCase = 1; Conversion = id 1513; Cleanup = cleanupId })
              Arguments = [ { Actual = acqActual; Formal = acqFormal; Abi = BoundaryScalar.Integer(32, true); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.ResourceHandle(resId, true)); ResultAdaptation = None
              Participants = Set.empty; SourceTypes = Map.empty }
        let emptyGraph = revision []
        let mkAcqGraph (callRow: BoundaryCall) =
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ acqSiteId, mkNode acqSiteId optHandleType (SemanticKind.Application(acqCalleeId, [ acqActual ])) [ acqCalleeId; acqActual ]
                          acqCalleeId, mkNode acqCalleeId unitType (SemanticKind.VarRef("fixture_open", Some acqBinding)) []
                          acqActual, mkNode acqActual intType (SemanticKind.VarRef("flags", None)) [] ]
                Emission =
                    { emptyGraph.Emission with
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ optHandleType, Result.Ok optHandleRep; ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations = Map.ofList [ acqSiteId, Result.Ok optHandleRep ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ acqDescId, acqImport ]
                                Calls = Map.ofList [ acqSiteId, callRow ]
                                ResourceDeclarations = Map.ofList [ resId, resDecl ] } } }
            |> declareTraversalReadings
        let runAcq (g: Revision) =
            let acc = MLIRAccumulator.empty ()
            MLIRAccumulator.bindNode acqActual (Arg 0) (TInt(IntWidth 32)) acc
            let res = matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus g g.Nodes[acqSiteId]) 64 acc
            Assert.Empty acc.AllOps
            Assert.True((MLIRAccumulator.recallNode acqSiteId acc).IsNone)
            res
        for badCall, expectedMsg in
            [ { acqCall with Entry = Some(id 1512) }, "Resource calls require their exact direct source invocation."
              { acqCall with Arguments = [] }, "Nullable resource acquisition differs from its declared native signature or result." ] do
            match runAcq (mkAcqGraph badCall) with
            | Result.Error reason ->
                Assert.Equal(expectedMsg, reason)
            | Result.Ok other -> failwithf "Admitted malformed AcquireNullable pResourceCall: %A" other

        let dirDescId = id 1520
        let dirBinding = id 1521
        let dirSiteId = id 1522
        let dirCalleeId = id 1523
        let dirFormal = id 1524
        let dirImport : BoundaryImport =
            { Identity = dirDescId; Binding = dirBinding; Scope = dirBinding
              Library = "fixture"; Symbol = "fixture_add1"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ dirBinding ]; Parameters = [ dirFormal, BoundaryScalar.Integer(32, true) ]
              Result = Some(BoundaryScalar.Integer(32, true)); Participants = Set.empty; SourceTypes = Map.empty; DeclarationFacts = Map.empty }
        let dirCall : BoundaryCall =
            { Site = dirSiteId; Import = dirDescId; Callee = dirCalleeId; Entry = None; Resource = None
              Arguments = []
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.Integer(32, true)); ResultAdaptation = None
              Participants = Set.empty; SourceTypes = Map.empty }
        let dirGraph =
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ dirSiteId, mkNode dirSiteId intType (SemanticKind.Application(dirCalleeId, [ acqActual ])) [ dirCalleeId; acqActual ]
                          dirCalleeId, mkNode dirCalleeId unitType (SemanticKind.VarRef("fixture_add1", Some dirBinding)) []
                          acqActual, mkNode acqActual intType (SemanticKind.VarRef("x", None)) [] ]
                Emission =
                    { emptyGraph.Emission with
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ dirDescId, dirImport ]
                                Calls = Map.ofList [ dirSiteId, dirCall ] } } }
            |> declareTraversalReadings
        let dirAcc = MLIRAccumulator.empty ()
        match matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus dirGraph dirGraph.Nodes[dirSiteId]) 64 dirAcc with
        | Result.Error reason ->
            Assert.Equal("Direct boundary calls require their exact direct signature and complete ordered actuals.", reason)
            Assert.Empty dirAcc.AllOps
            Assert.True((MLIRAccumulator.recallNode dirSiteId dirAcc).IsNone)
        | Result.Ok other -> failwithf "Admitted ordinary direct pBoundaryCall with omitted argument: %A" other

    [<Fact>]
    let ``non-ResourceHandle Entry callback import with CountedEntryArrays witnesses BoundaryFuncDecl and refuses ReadOnlyBufferDeclarations in callback`` () =
        let scopeId = id 1600
        let importId = id 1601
        let invId = id 1602
        let cbFormal = id 1603
        let countedId = id 1604
        let roDeclId = id 1605
        let contract : BAREWire.Descriptors.CountedEntryArrayDescriptor =
            { Binding = "Fixture.rowCb"; Parameter = 0; Argument = 1; CountArgument = 0
              Element = BAREWire.Descriptors.CountedElement.Handle "char*" }
        let countedRow : BoundaryCountedEntryArray =
            { Identity = countedId; Import = importId; Parameter = 0; Invocation = invId
              Contract = contract; DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let roDecl : BoundaryReadOnlyBufferDeclaration =
            { Identity = roDeclId; Declaration = id 1606; Body = id 1607; Formals = [ id 1608 ]; Descriptor = id 1609
              Parameter = 0; CountParameter = None; BufferFormal = id 1608; CountFormal = None
              Contract =
                { Binding = "Fixture.rowCb"; Parameter = 0
                  Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                  Hypothesis = { Identity = "fixture.rowcb.ro"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let mkInv (bytesCarrierId: NodeId) (argOrdinal: int) : BoundaryCallbackInvocation =
            { Identity = invId; Import = importId; Parameter = 0; Formal = cbFormal; Scope = scopeId
              Contract =
                { Binding = "Fixture.registerRowCb"; Parameter = 0; Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters =
                        [| { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32) }
                  Hypothesis = { Identity = "fixture.rowcb"; Version = "1"; Source = "component contract" } }
              Signature =
                { CallingConvention = "CDecl"
                  Parameters = [ BoundaryScalar.Integer(32, true); BoundaryScalar.ReadOnlyBytes bytesCarrierId ]
                  Result = Some(BoundaryScalar.Integer(32, true)) }
              Extent = BoundaryCallbackExtent.DuringCall; Participants = Set.singleton invId }
        let cbImport : BoundaryImport =
            { Identity = importId; Binding = scopeId; Scope = scopeId
              Library = "fixture"; Symbol = "fixture_register_row_cb"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ scopeId ]; Parameters = [ cbFormal, BoundaryScalar.Entry invId ]
              Result = Some(BoundaryScalar.Integer(32, true))
              Participants = Set.ofList [ scopeId; importId; invId; cbFormal ]
              SourceTypes = Map.empty; DeclarationFacts = Map.empty }
        let emptyGraph = revision []
        let goodBoundary =
            { emptyGraph.Emission.Boundary with
                Imports = Map.ofList [ importId, cbImport ]
                ByScope = Map.ofList [ scopeId, [ importId ] ]
                CountedEntryArrays = Map.ofList [ countedId, countedRow ]
                CallbackInvocations = Map.ofList [ invId, mkInv countedId 1 ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId goodBoundary with
        | Result.Ok [ MLIROp.FuncOp(FuncOp.BoundaryFuncDecl(imp, [ TFunc([ TInt(IntWidth 32); TMemRef(TInt(IntWidth 8)) ], [ TInt(IntWidth 32) ]) ], [ TInt(IntWidth 32) ])) as decl ] ->
            Assert.Equal(importId, imp.Identity)
            Assert.Equal(Result.Ok NeedsTargetRealization, Alex.Dialects.Core.Serialize.moduleText (Ok 64) None [ decl ])
        | other -> failwithf "Unexpected boundaryImportsAt result for non-ResourceHandle CountedEntryArrays callback: %A" other

        // Negative controls: ReadOnlyBufferDeclarations carrier or CountedEntryArrays wrong ordinal must be refused in callback signature
        let roInCallbackBoundary =
            { goodBoundary with
                ReadOnlyBufferDeclarations = Map.ofList [ roDeclId, roDecl ]
                CallbackInvocations = Map.ofList [ invId, mkInv roDeclId 1 ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId roInCallbackBoundary with
        | Result.Error reason ->
            Assert.Equal("A callback counted-entry array lacks its exact receiving invocation or parameter ordinal.", reason)
        | Result.Ok other -> failwithf "Admitted ReadOnlyBufferDeclarations carrier in callback signature: %A" other

        let wrongOrdinalBoundary =
            { goodBoundary with
                CountedEntryArrays = Map.ofList [ countedId, { countedRow with Contract = { contract with Argument = 0 } } ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId wrongOrdinalBoundary with
        | Result.Error reason ->
            Assert.Equal("A callback counted-entry array lacks its exact receiving invocation or parameter ordinal.", reason)
        | Result.Ok other -> failwithf "Admitted mismatched ordinal CountedEntryArrays in callback signature: %A" other

    [<Fact>]
    let ``ResourceImport validates non-ResourceHandle parameters and CountedEntryArrays callbacks`` () =
        let scopeId = id 1620
        let importId = id 1621
        let invId = id 1622
        let hFormal = id 1623
        let cbFormal = id 1624
        let cbHandleFormal = id 1625
        let countedId = id 1626
        let roDeclId = id 1627
        let contract : BAREWire.Descriptors.CountedEntryArrayDescriptor =
            { Binding = "Fixture.ctxRowCb"; Parameter = 1; Argument = 2; CountArgument = 1
              Element = BAREWire.Descriptors.CountedElement.Handle "char*" }
        let countedRow : BoundaryCountedEntryArray =
            { Identity = countedId; Import = importId; Parameter = 1; Invocation = invId
              Contract = contract; DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let roDecl : BoundaryReadOnlyBufferDeclaration =
            { Identity = roDeclId; Declaration = id 1628; Body = id 1629; Formals = [ id 1630 ]; Descriptor = id 1631
              Parameter = 1; CountParameter = None; BufferFormal = id 1630; CountFormal = None
              Contract =
                { Binding = "Fixture.ctxRowCb"; Parameter = 1
                  Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Retention = BAREWire.Descriptors.BufferRetention.DuringCall
                  Hypothesis = { Identity = "fixture.ctx.ro"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let mkInv (bytesCarrierId: NodeId) : BoundaryCallbackInvocation =
            { Identity = invId; Import = importId; Parameter = 1; Formal = cbFormal; Scope = scopeId
              Contract =
                { Binding = "Fixture.execWithCb"; Parameter = 1; Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters =
                        [| { Name = "ctx"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32) }
                  Hypothesis = { Identity = "fixture.ctx.cb"; Version = "1"; Source = "component contract" } }
              Signature =
                { CallingConvention = "CDecl"
                  Parameters = [ BoundaryScalar.ResourceHandle(cbHandleFormal, false); BoundaryScalar.Integer(32, true); BoundaryScalar.ReadOnlyBytes bytesCarrierId ]
                  Result = Some(BoundaryScalar.Integer(32, true)) }
              Extent = BoundaryCallbackExtent.DuringCall; Participants = Set.singleton invId }
        let resCbImport : BoundaryImport =
            { Identity = importId; Binding = scopeId; Scope = scopeId
              Library = "fixture"; Symbol = "fixture_exec_with_cb"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ scopeId ]
              Parameters = [ hFormal, BoundaryScalar.ResourceHandle(hFormal, false); cbFormal, BoundaryScalar.Entry invId ]
              Result = Some(BoundaryScalar.Integer(32, true))
              Participants = Set.ofList [ scopeId; importId; invId; hFormal; cbFormal ]
              SourceTypes = Map.empty; DeclarationFacts = Map.empty }
        let emptyGraph = revision []
        let goodBoundary =
            { emptyGraph.Emission.Boundary with
                Imports = Map.ofList [ importId, resCbImport ]
                ByScope = Map.ofList [ scopeId, [ importId ] ]
                CountedEntryArrays = Map.ofList [ countedId, countedRow ]
                CallbackInvocations = Map.ofList [ invId, mkInv countedId ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId goodBoundary with
        | Result.Ok [ MLIROp.ResourceImport imp ] -> Assert.Equal(importId, imp.Identity)
        | other -> failwithf "Unexpected ResourceImport result with valid CountedEntryArrays callback: %A" other

        let wrongInvBoundary =
            { goodBoundary with
                CountedEntryArrays = Map.ofList [ countedId, { countedRow with Invocation = id 1632 } ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId wrongInvBoundary with
        | Result.Error reason ->
            Assert.Equal("A callback counted-entry array lacks its exact receiving invocation or parameter ordinal.", reason)
        | Result.Ok other -> failwithf "Admitted ResourceImport callback with wrong Invocation CountedEntryArrays: %A" other

        let wrongOrdinalBoundary =
            { goodBoundary with
                CountedEntryArrays = Map.ofList [ countedId, { countedRow with Contract = { contract with Argument = 1 } } ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId wrongOrdinalBoundary with
        | Result.Error reason ->
            Assert.Equal("A callback counted-entry array lacks its exact receiving invocation or parameter ordinal.", reason)
        | Result.Ok other -> failwithf "Admitted ResourceImport callback with wrong Contract.Argument CountedEntryArrays: %A" other

        let roInCallbackBoundary =
            { goodBoundary with
                ReadOnlyBufferDeclarations = Map.ofList [ roDeclId, roDecl ]
                CallbackInvocations = Map.ofList [ invId, mkInv roDeclId ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId roInCallbackBoundary with
        | Result.Error reason ->
            Assert.Equal("A callback counted-entry array lacks its exact receiving invocation or parameter ordinal.", reason)
        | Result.Ok other -> failwithf "Admitted ResourceImport callback referencing ReadOnlyBufferDeclarations: %A" other

        let resWithTopLevelReadOnlyBytes =
            { resCbImport with
                Symbol = "fixture_exec_sql"
                Parameters = [ hFormal, BoundaryScalar.ResourceHandle(hFormal, false); cbFormal, BoundaryScalar.ReadOnlyBytes countedId ] }
        let topLevelCountedOnlyBoundary =
            { goodBoundary with
                Imports = Map.ofList [ importId, resWithTopLevelReadOnlyBytes ] }
        match Alex.Patterns.PlatformPatterns.boundaryImportsAt scopeId topLevelCountedOnlyBoundary with
        | Result.Error reason ->
            Assert.Equal("A read-only byte carrier lacks its exact source-published declaration.", reason)
        | Result.Ok other -> failwithf "Admitted ResourceImport top-level ReadOnlyBytes backed only by CountedEntryArrays: %A" other

    [<Fact>]
    let ``BorrowedResultView CompanionCall witnesses settled row incidence and refuses CompanionArguments mismatch`` () =
        let bvId = id 1750
        let declBinding = id 1751
        let bodyId = id 1752
        let descId = id 1753
        let ownerFormal = id 1754
        let siteId = id 1760
        let calleeId = id 1761
        let stmtBinding = id 1762
        let borrowOwnerRef = id 0
        let compOwnerRef = id 1764
        let invId = id 1765
        let readId = id 1766
        let scopeClaimId = id 1767
        let compSiteId = id 1768
        let compImportId = id 1769
        let support = Set.ofList [ bvId; declBinding; bodyId; descId; ownerFormal; siteId; calleeId; stmtBinding; borrowOwnerRef; compOwnerRef; invId; readId; scopeClaimId; compSiteId; compImportId ]
        let descFacts =
            let pCase = id 1790
            let arrId = id 1791
            Map.ofList
                [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                  ownerFormal, { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
                  arrId, { emptyFact "array" with References = [ ownerFormal ]; Children = [ ownerFormal ] }
                  descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let bvDecl : BoundaryBorrowedResultViewDeclaration =
            { Identity = bvId; Declaration = declBinding; Body = bodyId; Formals = [ ownerFormal ]; Descriptor = descId
              OwnerParameter = 0; OwnerFormal = ownerFormal
              Contract =
                { Binding = "Fixture.columnText"; Owner = 0
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Extent = BAREWire.Descriptors.BorrowedExtent.CompanionCall("Fixture.columnBytes", [| 0 |])
                  InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.OwnerCall { Binding = "Fixture.step"; Parameter = 0 } |]
                  Hypothesis = { Identity = "fixture.bv.origin"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let bvUse : BoundaryBorrowedResultViewUse =
            { Call = siteId; Declaration = bvId; Owner = borrowOwnerRef; View = siteId
              CompanionCall = Some compSiteId; CompanionArguments = [ compOwnerRef ]
              CallOrder = 10; Invalidations = [ invId ]; InvalidationOrders = [ 20 ]
              Reads = [ readId ]; ReadOrders = [ 12 ]; NullToNoneBoundary = true
              ScopeProof = scopeClaimId; Participants = ParticipantEvidence.Established [] }
        let scopeOb =
            obligation scopeClaimId "foreign-borrowed-view-scope"
                (ObligationBody.BorrowedResultViewScope
                    { Call = siteId; Declaration = bvId; Owner = borrowOwnerRef; View = siteId
                      CallOrder = 10; InvalidationOrders = [ 20 ]; ReadOrders = [ 12 ]
                      NullToNoneBoundary = true })
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding
              Library = "fixture"; Symbol = "fixture_column_text"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]; Parameters = [ ownerFormal, BoundaryScalar.ResourceHandle(ownerFormal, false) ]
              Result = Some(BoundaryScalar.BorrowedBytes bvId); Participants = support
              SourceTypes = Map.ofList [ ownerFormal, ptrHandleType ]
              DeclarationFacts = descFacts.Add(ownerFormal, { descFacts[ownerFormal] with SourceType = ptrHandleType }) }
        let compImport : BoundaryImport =
            { Identity = compImportId; Binding = id 1770; Scope = id 1770
              Library = "fixture"; Symbol = "fixture_column_bytes"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ id 1770 ]; Parameters = [ ownerFormal, BoundaryScalar.ResourceHandle(ownerFormal, false) ]
              Result = Some(BoundaryScalar.Integer(32, true)); Participants = Set.empty; SourceTypes = Map.empty; DeclarationFacts = Map.empty }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments = [ { Actual = borrowOwnerRef; Formal = ownerFormal; Abi = BoundaryScalar.ResourceHandle(ownerFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.BorrowedBytes bvId); ResultAdaptation = None
              Participants = support; SourceTypes = Map.empty }
        let compCall : BoundaryCall =
            { Site = compSiteId; Import = compImportId; Callee = id 1771; Entry = None; Resource = None
              Arguments = [ { Actual = compOwnerRef; Formal = ownerFormal; Abi = BoundaryScalar.ResourceHandle(ownerFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.Integer(32, true)); ResultAdaptation = None
              Participants = Set.empty; SourceTypes = Map.empty }
        let emptyGraph = revision []
        let mkGraph (companionArgs: NodeId list) =
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ borrowOwnerRef ])) [ calleeId; borrowOwnerRef ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_column_text", Some declBinding)) []
                          stmtBinding, mkNode stmtBinding ptrHandleType (SemanticKind.PatternBinding "stmt") []
                          borrowOwnerRef, mkNode borrowOwnerRef ptrHandleType (SemanticKind.VarRef("stmt", Some stmtBinding)) []
                          compOwnerRef, mkNode compOwnerRef ptrHandleType (SemanticKind.VarRef("stmt", Some stmtBinding)) []
                          scopeClaimId, mkNode scopeClaimId unitType (SemanticKind.Obligation scopeOb) [] ]
                Obligations = [ scopeOb ]
                Emission =
                    { emptyGraph.Emission with
                        Callable = { emptyGraph.Emission.Callable with AliasTargets = Map.ofList [ siteId, siteId ] }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ borrowOwnerRef, Result.Ok handleRep
                                          ownerFormal, Result.Ok handleRep
                                          siteId, Result.Ok bufRep ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow; compImportId, compImport ]
                                Calls = Map.ofList [ siteId, callRow; compSiteId, compCall ]
                                BorrowedResultViewDeclarations = Map.ofList [ bvId, bvDecl ]
                                BorrowedResultViewUses = Map.ofList [ siteId, { bvUse with CompanionArguments = companionArgs } ] } } }
        match runBoundaryCallAt siteId (mkGraph [ compOwnerRef ]) with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 1760, [ { SSA = Arg 0 } ], [], [], [ { Type = TMemRef(TInt(IntWidth 8)) } ]) ], TRValue _), _) -> ()
        | other -> failwithf "Unexpected BorrowedResultView CompanionCall settled incidence result: %A" other

        match runBoundaryCallAt siteId (mkGraph [ borrowOwnerRef ]) with
        | Result.Error reason ->
            Assert.Equal("Borrowed result view at boundary call 1760 lacks its exact non-owning declaration, invalidation frontier, or scope claim.", reason)
        | Result.Ok other -> failwithf "Admitted BorrowedResultView CompanionCall with CompanionArguments mismatch: %A" other

    [<Fact>]
    let ``BoundaryAbi.tryCallbackSignatureTypeAt derives closed callback ABI and fails closed on defective contracts`` () =
        let scopeId = id 1800
        let importId = id 1801
        let invId = id 1802
        let cbFormal = id 1803
        let countedId = id 1804
        let fnPtrType =
            TypeIdentity.Application(
                { Declaration = { Module = []; Name = "FnPtr" }
                  Parameters = [ TypeParamKind.Type ]
                  NativeKind = Some NTUKind.NTUfnptr },
                [ functionFrom ptrHandleType (functionFrom intType (functionFrom uint8Type intType)) ])
        let contract : BAREWire.Descriptors.CountedEntryArrayDescriptor =
            { Binding = "Fixture.cbCtx"; Parameter = 0; Argument = 2; CountArgument = 1
              Element = BAREWire.Descriptors.CountedElement.Handle "char*" }
        let countedRow : BoundaryCountedEntryArray =
            { Identity = countedId; Import = importId; Parameter = 0; Invocation = invId
              Contract = contract; DeclarationFacts = Map.empty; Participants = ParticipantEvidence.Established [] }
        let cbInv : BoundaryCallbackInvocation =
            { Identity = invId; Import = importId; Parameter = 0; Formal = cbFormal; Scope = scopeId
              Contract =
                { Binding = "Fixture.execCb"; Parameter = 0; Scope = "Fixture.scope"
                  Signature =
                    { CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                      Parameters =
                        [| { Name = "ctx"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argc"; Type = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32); PassBy = BAREWire.Descriptors.PassBy.Value }
                           { Name = "argv"; Type = BAREWire.Descriptors.TypeRef.Pointer 64; PassBy = BAREWire.Descriptors.PassBy.Value } |]
                      ReturnType = BAREWire.Descriptors.TypeRef.Integer(BAREWire.Descriptors.Signedness.Signed, 32) }
                  Hypothesis = { Identity = "fixture.cb.sig"; Version = "1"; Source = "component contract" } }
              Signature =
                { CallingConvention = "CDecl"
                  Parameters =
                    [ BoundaryScalar.ResourceHandle(cbFormal, false)
                      BoundaryScalar.Integer(32, true)
                      BoundaryScalar.ReadOnlyBytes countedId ]
                  Result = Some(BoundaryScalar.Integer(32, true)) }
              Extent = BoundaryCallbackExtent.DuringCall; Participants = Set.singleton invId }
        let cbImport : BoundaryImport =
            { Identity = importId; Binding = scopeId; Scope = scopeId
              Library = "fixture"; Symbol = "fixture_exec_cb"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ scopeId ]; Parameters = [ cbFormal, BoundaryScalar.Entry invId ]
              Result = Some(BoundaryScalar.Integer(32, true))
              Participants = Set.ofList [ scopeId; importId; invId; cbFormal ]
              SourceTypes = Map.ofList [ cbFormal, fnPtrType ]
              DeclarationFacts = Map.ofList [ cbFormal, { emptyFact "binding" with SourceType = fnPtrType } ] }
        let emptyGraph = revision []
        let graph =
            { emptyGraph with
                Emission =
                    { emptyGraph.Emission with
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ importId, cbImport ]
                                CountedEntryArrays = Map.ofList [ countedId, countedRow ]
                                CallbackInvocations = Map.ofList [ invId, cbInv ] }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ] } } }

        let expectedTy =
            TFunc(
                [ TOpaqueHandle(ptrHandleType, 64, 8)
                  TInt(IntWidth 32)
                  TMemRef(TInt(IntWidth 8)) ],
                [ TInt(IntWidth 32) ])
        Assert.Equal(Result.Ok expectedTy, BoundaryAbi.tryCallbackSignatureTypeAt graph invId)

        let missingInvGraph =
            { graph with Emission = { graph.Emission with Boundary = { graph.Emission.Boundary with CallbackInvocations = Map.empty } } }
        Assert.True((BoundaryAbi.tryCallbackSignatureTypeAt missingInvGraph invId).IsError)

        let nonCDeclGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                CallbackInvocations = Map.ofList [ invId, { cbInv with Signature = { cbInv.Signature with CallingConvention = "StdCall" } } ] } } }
        Assert.True((BoundaryAbi.tryCallbackSignatureTypeAt nonCDeclGraph invId).IsError)

        let resReturnGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                CallbackInvocations = Map.ofList [ invId, { cbInv with Signature = { cbInv.Signature with Result = Some(BoundaryScalar.ResourceHandle(cbFormal, false)) } } ] } } }
        Assert.True((BoundaryAbi.tryCallbackSignatureTypeAt resReturnGraph invId).IsError)

        let wrongOrdinalGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                CountedEntryArrays = Map.ofList [ countedId, { countedRow with Contract = { contract with Argument = 0 } } ] } } }
        Assert.True((BoundaryAbi.tryCallbackSignatureTypeAt wrongOrdinalGraph invId).IsError)

    [<Fact>]
    let ``BorrowedBytes Option witnessing admits settled option and union representations and refuses non-byte or invalid shapes`` () =
        let bvId = id 1850
        let declBinding = id 1851
        let bodyId = id 1852
        let descId = id 1853
        let ownerFormal = id 1854
        let siteId = id 1860
        let calleeId = id 1861
        let ownerActual = id 1862
        let invId = id 1863
        let readId = id 1864
        let scopeClaimId = id 1865
        let support = Set.ofList [ bvId; declBinding; bodyId; descId; ownerFormal; siteId; calleeId; ownerActual; invId; readId; scopeClaimId ]
        let descFacts =
            let pCase = id 1890
            let arrId = id 1891
            Map.ofList
                [ pCase, { emptyFact "case" with Text = [ "Value" ] }
                  ownerFormal, { emptyFact "record" with Text = [ "PassBy" ]; References = [ pCase ]; Children = [ pCase ] }
                  arrId, { emptyFact "array" with References = [ ownerFormal ]; Children = [ ownerFormal ] }
                  descId, { emptyFact "record" with Text = [ "Parameters" ]; References = [ arrId ]; Children = [ arrId ] } ]
        let bvDecl : BoundaryBorrowedResultViewDeclaration =
            { Identity = bvId; Declaration = declBinding; Body = bodyId; Formals = [ ownerFormal ]; Descriptor = descId
              OwnerParameter = 0; OwnerFormal = ownerFormal
              Contract =
                { Binding = "Fixture.columnTextOpt"; Owner = 0
                  Content = BAREWire.Descriptors.BorrowedContent.Utf8Text
                  Extent = BAREWire.Descriptors.BorrowedExtent.NulTerminated
                  InvalidatedBy = [| BAREWire.Descriptors.BorrowInvalidation.OwnerCall { Binding = "Fixture.step"; Parameter = 0 } |]
                  Hypothesis = { Identity = "fixture.bv.opt"; Version = "1"; Source = "component contract" } }
              DeclarationFacts = descFacts; Participants = ParticipantEvidence.Established [] }
        let bvUse : BoundaryBorrowedResultViewUse =
            { Call = siteId; Declaration = bvId; Owner = ownerActual; View = siteId
              CompanionCall = None; CompanionArguments = []
              CallOrder = 10; Invalidations = [ invId ]; InvalidationOrders = [ 20 ]
              Reads = [ readId ]; ReadOrders = [ 12 ]; NullToNoneBoundary = true
              ScopeProof = scopeClaimId; Participants = ParticipantEvidence.Established [] }
        let scopeOb =
            obligation scopeClaimId "foreign-borrowed-view-scope"
                (ObligationBody.BorrowedResultViewScope
                    { Call = siteId; Declaration = bvId; Owner = ownerActual; View = siteId
                      CallOrder = 10; InvalidationOrders = [ 20 ]; ReadOrders = [ 12 ]
                      NullToNoneBoundary = true })
        let importRow : BoundaryImport =
            { Identity = descId; Binding = declBinding; Scope = declBinding
              Library = "fixture"; Symbol = "fixture_column_text_opt"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ declBinding ]; Parameters = [ ownerFormal, BoundaryScalar.ResourceHandle(ownerFormal, false) ]
              Result = Some(BoundaryScalar.BorrowedBytes bvId); Participants = support
              SourceTypes = Map.ofList [ ownerFormal, ptrHandleType ]
              DeclarationFacts = descFacts.Add(ownerFormal, { descFacts[ownerFormal] with SourceType = ptrHandleType }) }
        let callRow : BoundaryCall =
            { Site = siteId; Import = descId; Callee = calleeId; Entry = None; Resource = None
              Arguments = [ { Actual = ownerActual; Formal = ownerFormal; Abi = BoundaryScalar.ResourceHandle(ownerFormal, false); Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []; Result = Some(BoundaryScalar.BorrowedBytes bvId); ResultAdaptation = None
              Participants = support; SourceTypes = Map.empty }
        let emptyGraph = revision []
        let mkGraph (siteRep: ValueRepresentation) =
            { emptyGraph with
                Nodes =
                    Map.ofList
                        [ siteId, mkNode siteId unitType (SemanticKind.Application(calleeId, [ ownerActual ])) [ calleeId; ownerActual ]
                          calleeId, mkNode calleeId unitType (SemanticKind.VarRef("fixture_column_text_opt", Some declBinding)) []
                          ownerActual, mkNode ownerActual ptrHandleType (SemanticKind.VarRef("stmt", None)) []
                          scopeClaimId, mkNode scopeClaimId unitType (SemanticKind.Obligation scopeOb) [] ]
                Obligations = [ scopeOb ]
                Emission =
                    { emptyGraph.Emission with
                        Callable = { emptyGraph.Emission.Callable with AliasTargets = Map.ofList [ siteId, siteId ] }
                        Numeric =
                            { emptyGraph.Emission.Numeric with
                                TypeRepresentations = Map.ofList [ ptrHandleType, Result.Ok handleRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ ownerActual, Result.Ok handleRep
                                          ownerFormal, Result.Ok handleRep
                                          siteId, Result.Ok siteRep ] }
                        Boundary =
                            { emptyGraph.Emission.Boundary with
                                Imports = Map.ofList [ descId, importRow ]
                                Calls = Map.ofList [ siteId, callRow ]
                                BorrowedResultViewDeclarations = Map.ofList [ bvId, bvDecl ]
                                BorrowedResultViewUses = Map.ofList [ siteId, bvUse ] } } }

        let optBufferRep = ValueRepresentation.Buffer(Some 48, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
        match runBoundaryCallAt siteId (mkGraph optBufferRep) with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 1860, [ { Type = TOpaqueHandle _ } ], [], [], [ { Type = TMemRefStatic(48, TInt(IntWidth 8)) } ]) ], TRValue { Type = TMemRefStatic(48, TInt(IntWidth 8)) }), _) -> ()
        | other -> failwithf "Unexpected BorrowedBytes settled option buffer result: %A" other

        let optUnionRep =
            ValueRepresentation.Union([ "None", []; "Some", [ bufRep ] ], Some(0, 24, 8))
        match runBoundaryCallAt siteId (mkGraph optUnionRep) with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(NodeId 1860, [ { Type = TOpaqueHandle _ } ], [], [], [ { Type = TMemRefStatic(24, TInt(IntWidth 8)) } ]) ], TRValue { Type = TMemRefStatic(24, TInt(IntWidth 8)) }), _) -> ()
        | other -> failwithf "Unexpected BorrowedBytes settled 2-case union option result: %A" other

        let badScalarRep = ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32"))
        match runBoundaryCallAt siteId (mkGraph badScalarRep) with
        | Result.Error reason -> Assert.Equal("Borrowed result view disagrees with its source-settled representation.", reason)
        | Result.Ok other -> failwithf "Admitted scalar BorrowedBytes result: %A" other

        let badUnionRep =
            ValueRepresentation.Union(
                [ "None", []; "Some", [ ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32")) ] ],
                Some(0, 16, 8))
        match runBoundaryCallAt siteId (mkGraph badUnionRep) with
        | Result.Error reason -> Assert.Equal("Borrowed result view disagrees with its source-settled representation.", reason)
        | Result.Ok other -> failwithf "Admitted non-byte union BorrowedBytes result: %A" other

        let zeroByteBufferRep = ValueRepresentation.Buffer(Some 0, ValueRepresentation.Scalar(SettledSlot.Integer(8, None)))
        match runBoundaryCallAt siteId (mkGraph zeroByteBufferRep) with
        | Result.Error reason -> Assert.Equal("Borrowed result view disagrees with its source-settled representation.", reason)
        | Result.Ok other -> failwithf "Admitted zero-extent BorrowedBytes option result: %A" other

    [<Fact>]
    let ``M10 SMTTransfer transcribes all five BAREWire SharedBufferPlacementObligation forms and refuses malformed obligations`` () =
        let space : BAREWire.Platform.MemorySpace =
            { Name = "ring_shm"
              Kind = BAREWire.Platform.MemoryKind.ViewBacked
              Capacity = 4096L
              Alignment = 64
              Granularity = 64
              Growth = BAREWire.Platform.Growth.Fixed
              Access = BAREWire.Platform.Access.ReadWrite
              Base = None
              Notes = ""
              MapKind = ""
              Since = ""
              Until = "" }
        let bufferSchema : BAREWire.Platform.BufferSchema =
            { Name = "RingSlotRing"
              Schema = "RingSlotRing"
              Capacity = 8L
              Framing = "unframed"
              Delimiter = 0
              TrimDelimiter = false
              Space = "ring_shm"
              Lifetime = "process"
              Access = BAREWire.Platform.Access.ReadWrite
              Slot = 0 }
        let structLayout : BAREWire.Hardware.StructDescriptor =
            { Name = "RingSlot"
              Layout =
                { Size = 8
                  Alignment = 4
                  Fields =
                    [| { Name = "Seq"
                         Offset = 0
                         Repr = BAREWire.Hardware.Repr.I32
                         Count = 1
                         Access = BAREWire.Hardware.AccessKind.ReadWrite
                         BitFields =
                           [| { Name = "FlagsLow"
                                Position = 0
                                Width = 4
                                Access = BAREWire.Hardware.AccessKind.ReadWrite }
                              { Name = "FlagsHigh"
                                Position = 4
                                Width = 4
                                Access = BAREWire.Hardware.AccessKind.ReadWrite } |]
                         Documentation = None }
                       { Name = "Payload"
                         Offset = 4
                         Repr = BAREWire.Hardware.Repr.I32
                         Count = 1
                         Access = BAREWire.Hardware.AccessKind.ReadWrite
                         BitFields = [||]
                         Documentation = None } |] }
              MayAlias = false
              FlexibleArray = None
              Documentation = None }
        let spaceDesc : BAREWire.Descriptors.MemorySpaceDescriptor =
            { Space = "ring_shm"
              MemoryRegion = BAREWire.Hardware.MemoryRegionKind.SRAM
              Access = "ReadWrite"
              ByteOrder = "little"
              ElementSize = 8
              ElementCount = 1
              RegionByteExtent = 8
              RegionAlignment = 64
              RegionLifetimeDepth = 1
              LibraryRetentionDepth = 2 }
        let viewLayout : BAREWire.Descriptors.ViewLayoutDescriptor =
            { Schema = "RingSlotRing"
              Element = BAREWire.Hardware.Repr.I32
              Alignment = 4
              Access = BAREWire.Hardware.AccessKind.ReadWrite }
        let placement : BAREWire.Platform.SharedBufferPlacement =
            { Name = "ring_slot_frames"
              SpaceDescriptor = spaceDesc
              SpaceOffset = 0L
              StructLayout = structLayout
              ViewLayout = viewLayout
              MeasuredElementSize = 8
              LayoutAlignment = 4
              LayoutByteOrder = "little"
              HasRawPointerFields = false
              HasVerifiedExports = true
              MappedDepth = 1
              FirstUseDepth = 1
              LastUseDepth = 2
              LibraryRetentionEndDepth = 2
              UnmapDepth = 3
              LeakedAtExit = false
              ConcurrentClefMutation = false
              LibraryMutatesBuffer = true
              OverlappingMutableShare = false
              MaxAccessedElementIndex = 0 }
        let desc : BAREWire.Platform.PlatformDescription =
            { Id = "test-ring-platform"
              DisplayName = "Test Ring Platform"
              Substrate = "cpu"
              Core = Some (BAREWire.Platform.TargetCore.create "linux" "x86_64" 64 "little" "glibc")
              Spaces = [| space |]
              ProgramLifetime = None
              Surfaces = [||]
              Buffers = [| bufferSchema |]
              Transports = [||]
              Lifecycle =
                { Clocks = [||]
                  Resets = [||]
                  Entry = ""
                  Teardown = ""
                  Persistence = BAREWire.Platform.Persistence.Volatile }
              Notes = [||]
              Limits = [||] }
        Assert.Empty(BAREWire.Platform.Check.checkSharedBufferPlacement desc placement)
        let rawObs = BAREWire.Platform.Obligations.sharedBufferObligations desc [| placement |]
        Assert.Equal(5, rawObs.Length)
        let extentBare = rawObs[0]
        let layoutBare = rawObs[1]
        let lifetimeBare = rawObs[2]
        let exclusivityBare = rawObs[3]
        let spaceBare = rawObs[4]
        let wrap (b: BAREWire.Platform.Obligation) : ObligationInfo =
            { Id = b.Id
              Kind = b.Kind
              Logic = b.Logic
              Statement = b.Statement
              Source = b.Source
              Refs = Array.toList b.Refs
              Body = ObligationBody.SharedBufferPlacementObligation b }
        let obs =
            [ wrap layoutBare
              wrap extentBare
              wrap spaceBare
              wrap lifetimeBare
              wrap exclusivityBare ]
        match Alex.Traversal.SMTTransfer.transfer obs with
        | Result.Error err -> Assert.Fail("Expected M10 SMTTransfer.transfer to succeed, got: " + err)
        | Result.Ok smtText ->
            Assert.Contains("fs9220_layout_ring_slot_frames", smtText)
            Assert.Contains("fs9221_extent_ring_slot_frames", smtText)
            Assert.Contains("fs9221_space_ring_shm", smtText)
            Assert.Contains("fs9222_lifetime_ring_slot_frames", smtText)
            Assert.Contains("fs9223_exclusivity_ring_slot_frames", smtText)
            Assert.Contains("smt.int.constant 4096", smtText)
            Assert.Contains("smt.int.constant 64", smtText)
            Assert.Contains("smt.check sat {} unknown {} unsat {}", smtText)

        let bareObsInOrder = [ layoutBare; extentBare; spaceBare; lifetimeBare; exclusivityBare ]
        for bareOb in bareObsInOrder do
            match Alex.Traversal.SMTTransfer.operations [ wrap bareOb ] with
            | Result.Error err -> Assert.Fail("Expected M10 SMTTransfer.operations to succeed, got: " + err)
            | Result.Ok ops ->
                let expectedConjuncts = BAREWire.Platform.Obligations.conclusionConjuncts bareOb
                let andClauseCounts =
                    ops
                    |> List.collect (function
                        | MLIROp.SMTOp(SMTOp.SMTSolver bodyOps) -> bodyOps
                        | other -> [ other ])
                    |> List.choose (function
                        | MLIROp.SMTOp(SMTOp.SMTAnd(_, clauses)) -> Some clauses.Length
                        | _ -> None)
                Assert.Equal(Some expectedConjuncts.Length, List.tryLast andClauseCounts)

        let assertSmtErrorSubstring (expectedSub: string) (res: Result<_, string>) =
            match res with
            | Result.Ok _ -> Assert.Fail("Expected SMTTransfer.operations to refuse mutant obligation with: " + expectedSub)
            | Result.Error msg -> Assert.Contains(expectedSub, msg)

        let badMeta = { wrap layoutBare with Id = "mismatched_id" }
        assertSmtErrorSubstring "disagrees with its BAREWire obligation metadata" (Alex.Traversal.SMTTransfer.operations [ badMeta ])

        let badSpace =
            wrap { spaceBare with Form = { spaceBare.Form with Values = [| -1L |] } }
        assertSmtErrorSubstring "SharedBufferSpaceExtent" (Alex.Traversal.SMTTransfer.operations [ badSpace ])

        let badSpaceNamesArity =
            wrap { spaceBare with Form = { spaceBare.Form with Names = [| "a"; "b" |]; Values = [| 0L; 8L |] } }
        assertSmtErrorSubstring "SharedBufferSpaceExtent" (Alex.Traversal.SMTTransfer.operations [ badSpaceNamesArity ])

        let badSpaceBlankName =
            wrap { spaceBare with Form = { spaceBare.Form with Names = [| "" |]; Values = [| 0L; 8L |] } }
        assertSmtErrorSubstring "SharedBufferSpaceExtent" (Alex.Traversal.SMTTransfer.operations [ badSpaceBlankName ])

        let badSpaceDupName =
            wrap { spaceBare with Form = { spaceBare.Form with Names = [| "dup"; "dup" |]; Values = [| 0L; 4L; 4L; 4L |] } }
        assertSmtErrorSubstring "SharedBufferSpaceExtent" (Alex.Traversal.SMTTransfer.operations [ badSpaceDupName ])

        let badLayout =
            wrap { layoutBare with Form = { layoutBare.Form with Values = [| 8L |] } }
        assertSmtErrorSubstring "invalid or duplicate BAREWire symbol bindings" (Alex.Traversal.SMTTransfer.operations [ badLayout ])

        let badLayoutTrailingSymbol =
            wrap
                { layoutBare with
                    Form =
                        { layoutBare.Form with
                            Names = Array.append layoutBare.Form.Names [| "field_off_2" |]
                            Values = Array.append layoutBare.Form.Values [| 8L |] } }
        assertSmtErrorSubstring "trailing field symbols beyond field count" (Alex.Traversal.SMTTransfer.operations [ badLayoutTrailingSymbol ])

    [<Fact>]
    let ``M10 shared-buffer zero-copy region witnessing emits memref views and refuses copy, permission, lifetime, and sync defects`` () =
        let modId = id 2000
        let fnId = id 2001
        let fdParamId = id 2002
        let bodySeqId = id 2003
        let mmapDeclId = id 2010
        let mmapDescId = id 2011
        let mmapFdFormal = id 2012
        let msyncDeclId = id 2020
        let msyncDescId = id 2021
        let msyncSlotFormal = id 2022
        let kickDeclId = id 2030
        let kickDescId = id 2031
        let kickSlotFormal = id 2032
        let munmapDeclId = id 2040
        let munmapDescId = id 2041
        let munmapSlotFormal = id 2042
        let mmapCallId = id 2050
        let mmapCalleeId = id 2051
        let mmapFdArgId = id 2052
        let slotBindId = id 2053
        let slotRefGetId = id 2054
        let getSeqId = id 2055
        let slotRefSetId = id 2056
        let val42Id = id 2057
        let setPayloadId = id 2058
        let slotRefMsyncId = id 2059
        let msyncCallId = id 2060
        let msyncCalleeId = id 2061
        let slotRefKickId = id 2062
        let kickCallId = id 2063
        let kickCalleeId = id 2064
        let slotRefMunmapId = id 2065
        let munmapCallId = id 2066
        let munmapCalleeId = id 2067
        let plId = id 2070
        let plDeclId = id 2071
        let spaceNodeId = id 2072
        let bufSchemaNodeId = id 2073
        let spaceDescNodeId = id 2074
        let structDescNodeId = id 2075
        let viewDescNodeId = id 2076
        let regionDescNodeId = id 2077
        let obLayoutId = id 2080
        let obExtentId = id 2081
        let obSpaceId = id 2082
        let obLifetimeId = id 2083
        let obExclusivityId = id 2084

        let ringSlotType =
            TypeIdentity.Application(
                { Declaration = { Module = [ "RingMod" ]; Name = "RingSlot" }
                  Parameters = []
                  NativeKind = None },
                [])
        let ringSlotRep =
            ValueRepresentation.Record(
                [ "Seq", ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32"))
                  "Payload", ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32")) ],
                Some([ 0; 4 ], 8, 4))
        let ringSlotLayout =
            SettledLayout.Record(
                [ { Name = "Seq"
                    Offset = Some 0
                    Size = Some 4
                    Align = Some 4
                    Slot = SettledSlot.Integer(32, Some "int32") }
                  { Name = "Payload"
                    Offset = Some 4
                    Size = Some 4
                    Align = Some 4
                    Slot = SettledSlot.Integer(32, Some "int32") } ],
                Some 8,
                Some 4)
        let space : BAREWire.Platform.MemorySpace =
            { Name = "ring_shm"
              Kind = BAREWire.Platform.MemoryKind.ViewBacked
              Capacity = 4096L
              Alignment = 64
              Granularity = 64
              Growth = BAREWire.Platform.Growth.Fixed
              Access = BAREWire.Platform.Access.ReadWrite
              Base = None
              Notes = ""
              MapKind = ""
              Since = ""
              Until = "" }
        let bufferSchema : BAREWire.Platform.BufferSchema =
            { Name = "RingSlotRing"
              Schema = "RingSlotRing"
              Capacity = 8L
              Framing = "unframed"
              Delimiter = 0
              TrimDelimiter = false
              Space = "ring_shm"
              Lifetime = "process"
              Access = BAREWire.Platform.Access.ReadWrite
              Slot = 0 }
        let structLayout : BAREWire.Hardware.StructDescriptor =
            { Name = "RingSlot"
              Layout =
                { Size = 8
                  Alignment = 4
                  Fields =
                    [| { Name = "Seq"
                         Offset = 0
                         Repr = BAREWire.Hardware.Repr.I32
                         Count = 1
                         Access = BAREWire.Hardware.AccessKind.ReadWrite
                         BitFields = [||]
                         Documentation = None }
                       { Name = "Payload"
                         Offset = 4
                         Repr = BAREWire.Hardware.Repr.I32
                         Count = 1
                         Access = BAREWire.Hardware.AccessKind.ReadWrite
                         BitFields = [||]
                         Documentation = None } |] }
              MayAlias = false
              FlexibleArray = None
              Documentation = None }
        let spaceDesc : BAREWire.Descriptors.MemorySpaceDescriptor =
            { Space = "ring_shm"
              MemoryRegion = BAREWire.Hardware.MemoryRegionKind.SRAM
              Access = "ReadWrite"
              ByteOrder = "little"
              ElementSize = 8
              ElementCount = 1
              RegionByteExtent = 8
              RegionAlignment = 64
              RegionLifetimeDepth = 1
              LibraryRetentionDepth = 2 }
        let viewLayout : BAREWire.Descriptors.ViewLayoutDescriptor =
            { Schema = "RingSlotRing"
              Element = BAREWire.Hardware.Repr.I32
              Alignment = 4
              Access = BAREWire.Hardware.AccessKind.ReadWrite }
        let barePlacement : BAREWire.Platform.SharedBufferPlacement =
            { Name = "ring_slot_frames"
              SpaceDescriptor = spaceDesc
              SpaceOffset = 0L
              StructLayout = structLayout
              ViewLayout = viewLayout
              MeasuredElementSize = 8
              LayoutAlignment = 4
              LayoutByteOrder = "little"
              HasRawPointerFields = false
              HasVerifiedExports = true
              MappedDepth = 1
              FirstUseDepth = 1
              LastUseDepth = 2
              LibraryRetentionEndDepth = 2
              UnmapDepth = 3
              LeakedAtExit = false
              ConcurrentClefMutation = false
              LibraryMutatesBuffer = true
              OverlappingMutableShare = false
              MaxAccessedElementIndex = 0 }
        let regionDesc : BAREWire.Descriptors.SharedBufferRegionDescriptor =
            { Placement = "ring_slot_frames"
              Acquire = "RingMod.mmapRing"
              Release = Some "RingMod.munmapRing"
              Sync = [| "RingMod.msyncRing" |]
              ForeignUses = [| "RingMod.ringKick" |] }
        let makePlacementDeclFacts
            (baseId: int)
            (p: BAREWire.Platform.SharedBufferPlacement)
            (rDesc: BAREWire.Descriptors.SharedBufferRegionDescriptor)
            (sp: BAREWire.Platform.MemorySpace)
            (buf: BAREWire.Platform.BufferSchema)
            : Map<NodeId, BoundaryDeclarationFact> =
            let s = p.SpaceDescriptor
            let mkFact form text numbers refs parent : BoundaryDeclarationFact =
                let nodeRefs = refs |> List.map NodeId
                { Form = form; Text = text; Numbers = numbers; References = nodeRefs; Children = nodeRefs; Parent = parent |> Option.map NodeId; SourceType = unitType }
            let mkStr fid value parent = fid, mkFact "string" [ value ] [] [] (Some parent)
            let mkInt fid (value: int64) parent = fid, mkFact "integer" [] [ bigint value ] [] (Some parent)
            let mkBool fid (value: bool) parent = fid, mkFact "boolean" [] [ if value then 1I else 0I ] [] (Some parent)
            let mkCase fid name refs parent = fid, mkFact "case" [ name ] [] refs (Some parent)
            let mkArr fid refs parent = fid, mkFact "array" [] [] refs (Some parent)
            let spNode = baseId + 2
            let bufNode = baseId + 3
            let sDescId = baseId + 4
            let stDescId = baseId + 5
            let vDescId = baseId + 6
            let rDescId = baseId + 7
            let recId = baseId + 20
            let pFields =
                [ "Name", mkStr (baseId + 21) p.Name recId
                  "SpaceDescriptor", (baseId + 38, mkFact "reference" [ "spaceDesc" ] [] [ sDescId ] (Some recId))
                  "SpaceOffset", mkInt (baseId + 22) p.SpaceOffset recId
                  "StructLayout", (baseId + 39, mkFact "reference" [ "structLayout" ] [] [ stDescId ] (Some recId))
                  "ViewLayout", (baseId + 40, mkFact "reference" [ "viewLayout" ] [] [ vDescId ] (Some recId))
                  "MeasuredElementSize", mkInt (baseId + 23) (int64 p.MeasuredElementSize) recId
                  "LayoutAlignment", mkInt (baseId + 24) (int64 p.LayoutAlignment) recId
                  "LayoutByteOrder", mkStr (baseId + 25) p.LayoutByteOrder recId
                  "HasRawPointerFields", mkBool (baseId + 26) p.HasRawPointerFields recId
                  "HasVerifiedExports", mkBool (baseId + 27) p.HasVerifiedExports recId
                  "MappedDepth", mkInt (baseId + 28) (int64 p.MappedDepth) recId
                  "FirstUseDepth", mkInt (baseId + 29) (int64 p.FirstUseDepth) recId
                  "LastUseDepth", mkInt (baseId + 30) (int64 p.LastUseDepth) recId
                  "LibraryRetentionEndDepth", mkInt (baseId + 31) (int64 p.LibraryRetentionEndDepth) recId
                  "UnmapDepth", mkInt (baseId + 32) (int64 p.UnmapDepth) recId
                  "LeakedAtExit", mkBool (baseId + 33) p.LeakedAtExit recId
                  "ConcurrentClefMutation", mkBool (baseId + 34) p.ConcurrentClefMutation recId
                  "LibraryMutatesBuffer", mkBool (baseId + 35) p.LibraryMutatesBuffer recId
                  "OverlappingMutableShare", mkBool (baseId + 36) p.OverlappingMutableShare recId
                  "MaxAccessedElementIndex", mkInt (baseId + 37) (int64 p.MaxAccessedElementIndex) recId ]
            let sFields =
                [ "Space", mkStr (baseId + 41) s.Space sDescId
                  "MemoryRegion", mkStr (baseId + 49) s.MemoryRegion sDescId
                  "Access", mkStr (baseId + 50) s.Access sDescId
                  "ByteOrder", mkStr (baseId + 42) s.ByteOrder sDescId
                  "ElementSize", mkInt (baseId + 43) (int64 s.ElementSize) sDescId
                  "ElementCount", mkInt (baseId + 44) (int64 s.ElementCount) sDescId
                  "RegionByteExtent", mkInt (baseId + 45) (int64 s.RegionByteExtent) sDescId
                  "RegionAlignment", mkInt (baseId + 46) (int64 s.RegionAlignment) sDescId
                  "RegionLifetimeDepth", mkInt (baseId + 47) (int64 s.RegionLifetimeDepth) sDescId
                  "LibraryRetentionDepth", mkInt (baseId + 48) (int64 s.LibraryRetentionDepth) sDescId ]
            let layoutRecId = baseId + 53
            let fieldsArrId = baseId + 56
            let fieldRecordsAndProps =
                p.StructLayout.Layout.Fields
                |> Array.toList
                |> List.mapi (fun idx df ->
                    let fRecId = baseId + 100 + idx * 10
                    let bfArrId = fRecId + 6
                    let ff =
                        [ "Name", mkStr (fRecId + 1) df.Name fRecId
                          "Offset", mkInt (fRecId + 2) (int64 df.Offset) fRecId
                          "Repr", mkStr (fRecId + 3) df.Repr fRecId
                          "Count", mkInt (fRecId + 4) (int64 df.Count) fRecId
                          "Access", mkStr (fRecId + 5) df.Access fRecId
                          "BitFields", mkArr bfArrId [] fRecId ]
                    let fRec = fRecId, mkFact "record" (ff |> List.map fst) [] (ff |> List.map (snd >> fst)) (Some fieldsArrId)
                    fRecId, fRec :: (ff |> List.map snd))
            let fRecIds = fieldRecordsAndProps |> List.map fst
            let fFactEntries = fieldRecordsAndProps |> List.collect snd
            let lFields =
                [ "Size", mkInt (baseId + 54) (int64 p.StructLayout.Layout.Size) layoutRecId
                  "Alignment", mkInt (baseId + 55) (int64 p.StructLayout.Layout.Alignment) layoutRecId
                  "Fields", mkArr fieldsArrId fRecIds layoutRecId ]
            let flexNoneId = baseId + 57
            let stFields =
                [ "Name", mkStr (baseId + 51) p.StructLayout.Name stDescId
                  "MayAlias", mkBool (baseId + 52) p.StructLayout.MayAlias stDescId
                  "FlexibleArray", mkCase flexNoneId "None" [] stDescId
                  "Layout", (layoutRecId, mkFact "record" (lFields |> List.map fst) [] (lFields |> List.map (snd >> fst)) (Some stDescId)) ]
            let vFields =
                [ "Schema", mkStr (baseId + 61) p.ViewLayout.Schema vDescId
                  "Element", mkStr (baseId + 63) p.ViewLayout.Element vDescId
                  "Alignment", mkInt (baseId + 62) (int64 p.ViewLayout.Alignment) vDescId
                  "Access", mkStr (baseId + 64) p.ViewLayout.Access vDescId ]
            let spNodeFields =
                [ "Name", mkStr (baseId + 71) sp.Name spNode
                  "Kind", mkStr (baseId + 72) sp.Kind spNode
                  "Capacity", mkInt (baseId + 73) sp.Capacity spNode
                  "Alignment", mkInt (baseId + 74) (int64 sp.Alignment) spNode
                  "Granularity", mkInt (baseId + 75) (int64 sp.Granularity) spNode
                  "Growth", mkStr (baseId + 76) sp.Growth spNode
                  "Access", mkStr (baseId + 77) sp.Access spNode
                  "Base", mkCase (baseId + 151) "None" [] spNode
                  "Notes", mkStr (baseId + 152) sp.Notes spNode
                  "MapKind", mkStr (baseId + 153) sp.MapKind spNode
                  "Since", mkStr (baseId + 154) sp.Since spNode
                  "Until", mkStr (baseId + 155) sp.Until spNode ]
            let bufNodeFields =
                [ "Name", mkStr (baseId + 81) buf.Name bufNode
                  "Schema", mkStr (baseId + 82) buf.Schema bufNode
                  "Capacity", mkInt (baseId + 83) buf.Capacity bufNode
                  "Framing", mkStr (baseId + 84) buf.Framing bufNode
                  "Delimiter", mkInt (baseId + 156) (int64 buf.Delimiter) bufNode
                  "TrimDelimiter", mkBool (baseId + 85) buf.TrimDelimiter bufNode
                  "Space", mkStr (baseId + 86) buf.Space bufNode
                  "Lifetime", mkStr (baseId + 157) buf.Lifetime bufNode
                  "Access", mkStr (baseId + 87) buf.Access bufNode
                  "Slot", mkInt (baseId + 158) (int64 buf.Slot) bufNode ]
            let relOptFactId = baseId + 93
            let relInnerId = baseId + 94
            let relField, relExtra =
                match rDesc.Release with
                | None -> mkCase relOptFactId "None" [] rDescId, []
                | Some relStr -> mkCase relOptFactId "Some" [ relInnerId ] rDescId, [ mkStr relInnerId relStr relOptFactId ]
            let syncFactPairs =
                rDesc.Sync
                |> Array.toList
                |> List.mapi (fun idx s ->
                    let sid = baseId + 160 + idx
                    sid, mkStr sid s (baseId + 95))
            let fuFactPairs =
                rDesc.ForeignUses
                |> Array.toList
                |> List.mapi (fun idx f ->
                    let fid = baseId + 180 + idx
                    fid, mkStr fid f (baseId + 97))
            let regNodeFields =
                [ "Placement", mkStr (baseId + 91) rDesc.Placement rDescId
                  "Acquire", mkStr (baseId + 92) rDesc.Acquire rDescId
                  "Release", relField
                  "Sync", mkArr (baseId + 95) (syncFactPairs |> List.map fst) rDescId
                  "ForeignUses", mkArr (baseId + 97) (fuFactPairs |> List.map fst) rDescId ]
            let allEntries =
                [ baseId, mkFact "quotation" [] [] [ recId ] (Some (baseId + 1))
                  baseId + 1, mkFact "binding" [ p.Name ] [ 0I; 0I ] [ baseId ] None
                  spNode, mkFact "record" (spNodeFields |> List.map fst) [] (spNodeFields |> List.map (snd >> fst)) None
                  bufNode, mkFact "record" (bufNodeFields |> List.map fst) [] (bufNodeFields |> List.map (snd >> fst)) None
                  sDescId, mkFact "record" (sFields |> List.map fst) [] (sFields |> List.map (snd >> fst)) None
                  stDescId, mkFact "record" (stFields |> List.map fst) [] (stFields |> List.map (snd >> fst)) None
                  vDescId, mkFact "record" (vFields |> List.map fst) [] (vFields |> List.map (snd >> fst)) None
                  rDescId, mkFact "record" (regNodeFields |> List.map fst) [] (regNodeFields |> List.map (snd >> fst)) None
                  recId, mkFact "record" (pFields |> List.map fst) [] (pFields |> List.map (snd >> fst)) (Some baseId) ]
                @ (pFields |> List.map snd)
                @ (sFields |> List.map snd)
                @ (stFields |> List.map snd)
                @ (lFields |> List.map snd)
                @ fFactEntries
                @ (vFields |> List.map snd)
                @ (spNodeFields |> List.map snd)
                @ (bufNodeFields |> List.map snd)
                @ (regNodeFields |> List.map snd)
                @ relExtra
                @ (syncFactPairs |> List.map snd)
                @ (fuFactPairs |> List.map snd)
            allEntries |> List.map (fun (fid, f) -> NodeId fid, f) |> Map.ofList

        let desc : BAREWire.Platform.PlatformDescription =
            { Id = "test-ring-platform"
              DisplayName = "Test Ring Platform"
              Substrate = "cpu"
              Core = Some (BAREWire.Platform.TargetCore.create "linux" "x86_64" 64 "little" "glibc")
              Spaces = [| space |]
              ProgramLifetime = None
              Surfaces = [||]
              Buffers = [| bufferSchema |]
              Transports = [||]
              Lifecycle =
                { Clocks = [||]
                  Resets = [||]
                  Entry = ""
                  Teardown = ""
                  Persistence = BAREWire.Platform.Persistence.Volatile }
              Notes = [||]
              Limits = [||] }
        let rawObs = BAREWire.Platform.Obligations.sharedBufferObligations desc [| barePlacement |]
        let extentBare, layoutBare, lifetimeBare, exclusivityBare, spaceBare =
            match Array.toList rawObs with
            | [ o0; o1; o2; o3; o4 ] -> o0, o1, o2, o3, o4
            | _ -> failwith "Unexpected shared-buffer obligation count"
        let mkOb (b: BAREWire.Platform.Obligation) : ObligationInfo =
            { Id = b.Id
              Kind = b.Kind
              Logic = b.Logic
              Statement = b.Statement
              Source = b.Source
              Refs = Array.toList b.Refs
              Body = ObligationBody.SharedBufferPlacementObligation b }
        let obLayout = mkOb layoutBare
        let obExtent = mkOb extentBare
        let obSpace = mkOb spaceBare
        let obLifetime = mkOb lifetimeBare
        let obExclusivity = mkOb exclusivityBare
        let allObs = [ obLayout; obExtent; obSpace; obLifetime; obExclusivity ]
        let currentClaims =
            Map.ofList
                [ obLayoutId, obLayout
                  obExtentId, obExtent
                  obSpaceId, obSpace
                  obLifetimeId, obLifetime
                  obExclusivityId, obExclusivity ]

        let mkImportBindingFact (shortName: string) (ty: TypeIdentity) : BoundaryDeclarationFact =
            { Form = "binding"
              Text = [ shortName ]
              Numbers = [ 0I; 0I ]
              References = []
              Children = []
              Parent = Some modId
              SourceType = ty }
        let mmapImport : BoundaryImport =
            { Identity = mmapDescId; Binding = mmapDeclId; Scope = modId
              Library = "ring"; Symbol = "mmap_ring"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ modId; mmapDeclId ]
              Parameters = [ mmapFdFormal, BoundaryScalar.Integer(32, true) ]
              Result = Some(BoundaryScalar.Integer(64, false))
              Participants = Set.ofList [ modId; mmapDeclId; mmapDescId; mmapFdFormal ]
              SourceTypes = Map.ofList [ mmapDeclId, functionFrom intType ringSlotType; mmapFdFormal, intType ]
              DeclarationFacts =
                Map.ofList
                    [ mmapDeclId, mkImportBindingFact "mmapRing" (functionFrom intType ringSlotType)
                      mmapFdFormal, { emptyFact "binding" with SourceType = intType } ] }
        let mkSlotImport (descId: NodeId) (declId: NodeId) (slotFormal: NodeId) (clefName: string) (sym: string) : BoundaryImport =
            { Identity = descId; Binding = declId; Scope = modId
              Library = "ring"; Symbol = sym; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ modId; declId ]
              Parameters = [ slotFormal, BoundaryScalar.ResourceHandle(slotFormal, false) ]
              Result = None
              Participants = Set.ofList [ modId; declId; descId; slotFormal ]
              SourceTypes = Map.ofList [ declId, functionFrom ringSlotType unitType; slotFormal, ringSlotType ]
              DeclarationFacts =
                Map.ofList
                    [ declId, mkImportBindingFact clefName (functionFrom ringSlotType unitType)
                      slotFormal, { emptyFact "binding" with SourceType = ringSlotType } ] }
        let msyncImport = mkSlotImport msyncDescId msyncDeclId msyncSlotFormal "msyncRing" "msync_ring"
        let kickImport = mkSlotImport kickDescId kickDeclId kickSlotFormal "ringKick" "ring_kick"
        let munmapImport = mkSlotImport munmapDescId munmapDeclId munmapSlotFormal "munmapRing" "munmap_ring"

        let mmapCall : BoundaryCall =
            { Site = mmapCallId; Import = mmapDescId; Callee = mmapCalleeId; Entry = None; Resource = None
              Arguments =
                [ { Actual = mmapFdArgId; Formal = mmapFdFormal
                    Abi = BoundaryScalar.Integer(32, true)
                    Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []
              Result = Some(BoundaryScalar.Integer(64, false))
              ResultAdaptation = None
              Participants = Set.ofList [ mmapCallId; mmapCalleeId; mmapFdArgId ]
              SourceTypes = Map.empty }
        let mkSlotCall (site: NodeId) (descId: NodeId) (callee: NodeId) (actual: NodeId) (formal: NodeId) : BoundaryCall =
            { Site = site; Import = descId; Callee = callee; Entry = None; Resource = None
              Arguments =
                [ { Actual = actual; Formal = formal
                    Abi = BoundaryScalar.ResourceHandle(formal, false)
                    Adaptation = None; OptionalEntry = None; BufferAbsence = None } ]
              ErasedUnitArguments = []
              Result = None
              ResultAdaptation = None
              Participants = Set.ofList [ site; callee; actual ]
              SourceTypes = Map.empty }
        let msyncCall = mkSlotCall msyncCallId msyncDescId msyncCalleeId slotRefMsyncId msyncSlotFormal
        let kickCall = mkSlotCall kickCallId kickDescId kickCalleeId slotRefKickId kickSlotFormal
        let munmapCall = mkSlotCall munmapCallId munmapDescId munmapCalleeId slotRefMunmapId munmapSlotFormal

        let placementParticipants =
            [ 2070 .. 2077 ]
            |> List.mapi (fun idx nid -> { Role = ParticipantRole.Site; Node = NodeId nid; Ordinal = idx; Group = plId })
        let placement : BoundarySharedBufferPlacementDeclaration =
            { Identity = plId
              Declaration = plDeclId
              SpaceNode = spaceNodeId
              BufferSchemaNode = bufSchemaNodeId
              SpaceDescriptorNode = spaceDescNodeId
              StructDescriptorNode = structDescNodeId
              ViewDescriptorNode = viewDescNodeId
              RegionDescriptorNode = regionDescNodeId
              Placement = barePlacement
              RegionDescriptor = regionDesc
              Space = space
              BufferSchema = bufferSchema
              PlatformEndianness = "little"
              Obligations = [ obLayoutId; obExtentId; obSpaceId; obLifetimeId; obExclusivityId ]
              DeclarationFacts = makePlacementDeclFacts 2070 barePlacement regionDesc space bufferSchema
              Participants = ParticipantEvidence.Established placementParticipants }
        let useParticipantNodes =
            [ getSeqId
              plId
              mmapCallId
              munmapCallId
              msyncCallId
              kickCallId
              setPayloadId
              obLayoutId
              obExtentId
              obSpaceId
              obLifetimeId
              obExclusivityId ]
        let viewUse : BoundarySharedBufferViewUse =
            { Site = getSeqId
              PlacementDeclaration = plId
              ElementType = ringSlotType
              ElementSlot = SettledSlot.InlineBytes(8, 4)
              RegionAcquisitionCall = mmapCallId
              RegionReleaseCall = Some munmapCallId
              SyncCalls = [ msyncCallId ]
              ForeignUseCalls = [ kickCallId ]
              ViewProjections = [ getSeqId ]
              WriteProjections = [ setPayloadId ]
              AcquisitionOrder = 1
              ProjectionOrders = [ 2 ]
              WriteProjectionOrders = [ 3 ]
              SyncOrders = [ 4 ]
              ForeignUseOrders = [ 5 ]
              ReleaseOrder = Some 6
              Copies = 0
              LayoutObligation = obLayoutId
              ExtentObligation = obExtentId
              SpaceExtentObligation = obSpaceId
              LifetimeObligation = obLifetimeId
              ExclusivityObligation = obExclusivityId
              Participants =
                ParticipantEvidence.Established
                    (useParticipantNodes
                     |> List.mapi (fun idx n -> { Role = ParticipantRole.Site; Node = n; Ordinal = idx; Group = getSeqId })) }

        let platformPremise : BoundaryPlatformPremise =
            { Id = "test-ring-platform"
              Description = None
              Loading = None
              LibraryPath = None
              SourcePaths = Set.empty
              Architecture = Some "x86_64"
              OS = Some "linux"
              Endianness = Some "little"
              RuntimeClaim = None
              Substrate = None
              Dimensions = Map.empty
              Representations = Map.empty
              EndpointReturns = Map.empty
              Spaces = [ space ]
              Buffers = [ bufferSchema ]
              SharedBufferRegions = [ regionDesc ] }
        let boundaryDomain : BoundaryDomain =
            { ResourceEvidence = None
              Premises = Map.empty
              Platform = Some platformPremise
              Meets = Map.empty
              Declarations = []
              WritableBufferDeclarations = []
              WritableBufferUses = []
              ReadOnlyBufferDeclarations = []
              ReadOnlyBufferUses = []
              BorrowedResultViewDeclarations = []
              BorrowedResultViewUses = []
              BufferAbsences = []
              CountedEntryArrays = []
              ResourceDeclarations = []
              ResourceAccesses = []
              ResourceEvaluationRoots = []
              ResourceEvaluationRelations = []
              Imports = []
              Loading = None
              Entries = []
              Calls = []
              ByteViews = []
              StringExtents = []
              StringOriginRelations = None
              StringOriginRoots = None
              StringComparisons = []
              StringLengthComparisons = []
              StringComparisonReads = []
              StringBorrowSnapshots = []
              StringBorrowCopies = []
              StringBorrowAllocations = []
              IntrinsicDeclarations = []
              IntrinsicImports = []
              IntrinsicCalls = []
              IntrinsicProofs = []
              StringStorage = None
              DeclarationLeaves = Set.empty
              DeclarationOnly = Set.empty
              Links = Set.empty
              Failures = []
              ResultHypotheses = []
              CallbackInvocations = []
              CallbackAbsences = []
              ClosedEntries = [] }
        let domainEdge : Hyperedge =
            { Class = EdgeClass.Boundary
              Role = EdgeRole.BoundaryDomain boundaryDomain
              Ordinal = 0
              Sources = []
              Target = modId }

        let i32Rep = ValueRepresentation.Scalar(SettledSlot.Integer(32, Some "int32"))
        let unitRep = ValueRepresentation.Scalar SettledSlot.Unit
        let baseGraph = revision []
        let mkNodeWithParent nid ty kind children parentOpt =
            { mkNode nid ty kind children with Parent = parentOpt }
        let graph : Revision =
            { baseGraph with
                Edges = [ domainEdge ]
                Nodes =
                    Map.ofList
                        [ modId, mkNodeWithParent modId unitType (SemanticKind.ModuleDef("RingMod", [ fnId ])) [] None
                          fnId, mkNodeWithParent fnId (functionFrom intType intType) (SemanticKind.Lambda([ "fd", intType, fdParamId ], bodySeqId, [], None, LambdaContext.RegularClosure)) [ fdParamId; bodySeqId ] (Some modId)
                          fdParamId, mkNodeWithParent fdParamId intType (SemanticKind.PatternBinding "fd") [] (Some fnId)
                          bodySeqId, mkNodeWithParent bodySeqId intType (SemanticKind.Sequential [ slotBindId; getSeqId; setPayloadId; msyncCallId; kickCallId; munmapCallId ]) [ slotBindId; getSeqId; setPayloadId; msyncCallId; kickCallId; munmapCallId ] (Some fnId)
                          slotBindId, mkNodeWithParent slotBindId ringSlotType (SemanticKind.Binding("slot", false, false, None)) [ mmapCallId ] (Some bodySeqId)
                          mmapCallId, mkNodeWithParent mmapCallId ringSlotType (SemanticKind.Application(mmapCalleeId, [ mmapFdArgId ])) [ mmapCalleeId; mmapFdArgId ] (Some slotBindId)
                          mmapCalleeId, mkNodeWithParent mmapCalleeId (functionFrom intType ringSlotType) (SemanticKind.VarRef("mmapRing", Some mmapDeclId)) [] (Some mmapCallId)
                          mmapFdArgId, mkNodeWithParent mmapFdArgId intType (SemanticKind.VarRef("fd", Some fdParamId)) [] (Some mmapCallId)
                          slotRefGetId, mkNodeWithParent slotRefGetId ringSlotType (SemanticKind.VarRef("slot", Some slotBindId)) [] (Some getSeqId)
                          getSeqId, mkNodeWithParent getSeqId intType (SemanticKind.FieldGet(slotRefGetId, "Seq")) [ slotRefGetId ] (Some bodySeqId)
                          slotRefSetId, mkNodeWithParent slotRefSetId ringSlotType (SemanticKind.VarRef("slot", Some slotBindId)) [] (Some setPayloadId)
                          val42Id, mkNodeWithParent val42Id intType (SemanticKind.Literal(NativeLiteral.Int(42L, NTUKind.NTUint(NTUWidth.Fixed 32)))) [] (Some setPayloadId)
                          setPayloadId, mkNodeWithParent setPayloadId unitType (SemanticKind.FieldSet(slotRefSetId, "Payload", val42Id)) [ slotRefSetId; val42Id ] (Some bodySeqId)
                          slotRefMsyncId, mkNodeWithParent slotRefMsyncId ringSlotType (SemanticKind.VarRef("slot", Some slotBindId)) [] (Some msyncCallId)
                          msyncCallId, mkNodeWithParent msyncCallId unitType (SemanticKind.Application(msyncCalleeId, [ slotRefMsyncId ])) [ msyncCalleeId; slotRefMsyncId ] (Some bodySeqId)
                          msyncCalleeId, mkNodeWithParent msyncCalleeId (functionFrom ringSlotType unitType) (SemanticKind.VarRef("msyncRing", Some msyncDeclId)) [] (Some msyncCallId)
                          slotRefKickId, mkNodeWithParent slotRefKickId ringSlotType (SemanticKind.VarRef("slot", Some slotBindId)) [] (Some kickCallId)
                          kickCallId, mkNodeWithParent kickCallId unitType (SemanticKind.Application(kickCalleeId, [ slotRefKickId ])) [ kickCalleeId; slotRefKickId ] (Some bodySeqId)
                          kickCalleeId, mkNodeWithParent kickCalleeId (functionFrom ringSlotType unitType) (SemanticKind.VarRef("ringKick", Some kickDeclId)) [] (Some kickCallId)
                          slotRefMunmapId, mkNodeWithParent slotRefMunmapId ringSlotType (SemanticKind.VarRef("slot", Some slotBindId)) [] (Some munmapCallId)
                          munmapCallId, mkNodeWithParent munmapCallId unitType (SemanticKind.Application(munmapCalleeId, [ slotRefMunmapId ])) [ munmapCalleeId; slotRefMunmapId ] (Some bodySeqId)
                          munmapCalleeId, mkNodeWithParent munmapCalleeId (functionFrom ringSlotType unitType) (SemanticKind.VarRef("munmapRing", Some munmapDeclId)) [] (Some munmapCallId)
                          obLayoutId, mkNode obLayoutId unitType (SemanticKind.Obligation obLayout) []
                          obExtentId, mkNode obExtentId unitType (SemanticKind.Obligation obExtent) []
                          obSpaceId, mkNode obSpaceId unitType (SemanticKind.Obligation obSpace) []
                          obLifetimeId, mkNode obLifetimeId unitType (SemanticKind.Obligation obLifetime) []
                          obExclusivityId, mkNode obExclusivityId unitType (SemanticKind.Obligation obExclusivity) [] ]
                Obligations = allObs
                CurrentClaims = currentClaims
                Emission =
                    { baseGraph.Emission with
                        Callable =
                            { baseGraph.Emission.Callable with
                                Symbols =
                                    Map.ofList
                                        [ mmapDeclId, CallableSymbolName.ModuleBinding("RingMod", "mmapRing")
                                          msyncDeclId, CallableSymbolName.ModuleBinding("RingMod", "msyncRing")
                                          kickDeclId, CallableSymbolName.ModuleBinding("RingMod", "ringKick")
                                          munmapDeclId, CallableSymbolName.ModuleBinding("RingMod", "munmapRing") ]
                                AliasTargets =
                                    Map.ofList
                                        [ mmapCallId, mmapCallId
                                          slotBindId, mmapCallId
                                          slotRefGetId, mmapCallId
                                          slotRefSetId, mmapCallId
                                          slotRefMsyncId, mmapCallId
                                          slotRefKickId, mmapCallId
                                          slotRefMunmapId, mmapCallId
                                          getSeqId, getSeqId
                                          setPayloadId, setPayloadId
                                          msyncCallId, msyncCallId
                                          kickCallId, kickCallId
                                          munmapCallId, munmapCallId ] }
                        Numeric =
                            { baseGraph.Emission.Numeric with
                                SourceTypes =
                                    Map.ofList
                                        [ mmapCallId, ringSlotType
                                          slotBindId, ringSlotType
                                          slotRefGetId, ringSlotType
                                          slotRefSetId, ringSlotType
                                          slotRefMsyncId, ringSlotType
                                          slotRefKickId, ringSlotType
                                          slotRefMunmapId, ringSlotType ]
                                Layouts = Map.ofList [ ringSlotType, ringSlotLayout ]
                                TypeRepresentations =
                                    Map.ofList
                                        [ ringSlotType, Result.Ok ringSlotRep
                                          intType, Result.Ok i32Rep
                                          unitType, Result.Ok unitRep ]
                                OccurrenceRepresentations =
                                    Map.ofList
                                        [ fdParamId, Result.Ok i32Rep
                                          mmapFdArgId, Result.Ok i32Rep
                                          mmapFdFormal, Result.Ok i32Rep
                                          mmapCallId, Result.Ok ringSlotRep
                                          slotBindId, Result.Ok ringSlotRep
                                          slotRefGetId, Result.Ok ringSlotRep
                                          slotRefSetId, Result.Ok ringSlotRep
                                          slotRefMsyncId, Result.Ok ringSlotRep
                                          slotRefKickId, Result.Ok ringSlotRep
                                          slotRefMunmapId, Result.Ok ringSlotRep
                                          msyncSlotFormal, Result.Ok ringSlotRep
                                          kickSlotFormal, Result.Ok ringSlotRep
                                          munmapSlotFormal, Result.Ok ringSlotRep
                                          getSeqId, Result.Ok i32Rep
                                          val42Id, Result.Ok i32Rep
                                          setPayloadId, Result.Ok unitRep
                                          msyncCallId, Result.Ok unitRep
                                          kickCallId, Result.Ok unitRep
                                          munmapCallId, Result.Ok unitRep
                                          bodySeqId, Result.Ok i32Rep ] }
                        Boundary =
                            { baseGraph.Emission.Boundary with
                                ByScope = Map.ofList [ modId, [ mmapDescId; msyncDescId; kickDescId; munmapDescId ] ]
                                Imports =
                                    Map.ofList
                                        [ mmapDescId, mmapImport
                                          msyncDescId, msyncImport
                                          kickDescId, kickImport
                                          munmapDescId, munmapImport ]
                                Calls =
                                    Map.ofList
                                        [ mmapCallId, mmapCall
                                          msyncCallId, msyncCall
                                          kickCallId, kickCall
                                          munmapCallId, munmapCall ]
                                SharedBufferPlacements = Map.ofList [ plId, placement ]
                                SharedBufferViewUses = Map.ofList [ getSeqId, viewUse ] } } }
            |> declareTraversalReadings

        let sharedIntegrityViolations =
            Fidelity.PSG.Integrity.check graph
            |> List.filter (fun v ->
                v.Part.StartsWith("Emission.Boundary.SharedBufferPlacements")
                || v.Part.StartsWith("Emission.Boundary.SharedBufferViewUses"))
        Assert.Empty(sharedIntegrityViolations)

        let expectedStructTy =
            TStruct(
                [ "Seq", TInt(IntWidth 32); "Payload", TInt(IntWidth 32) ],
                Some { Offsets = [ 0; 4 ]; Size = 8; Align = 4 })

        match Alex.Patterns.PlatformPatterns.boundaryImportsIn modId graph with
        | Result.Error err -> Assert.Fail("Expected boundaryImportsIn to succeed, got: " + err)
        | Result.Ok importOps ->
            Assert.Equal(4, importOps.Length)
            let expectedImportOps : MLIROp list =
                [ MLIROp.FuncOp(FuncOp.BoundaryFuncDecl(mmapImport, [ TInt(IntWidth 32) ], [ expectedStructTy ]))
                  MLIROp.FuncOp(FuncOp.BoundaryFuncDecl(msyncImport, [ expectedStructTy ], []))
                  MLIROp.FuncOp(FuncOp.BoundaryFuncDecl(kickImport, [ expectedStructTy ], []))
                  MLIROp.FuncOp(FuncOp.BoundaryFuncDecl(munmapImport, [ expectedStructTy ], [])) ]
            Assert.Equal<MLIROp list>(expectedImportOps, importOps)
            Assert.Equal(
                Result.Ok ModuleText.NeedsTargetRealization,
                Alex.Dialects.Core.Serialize.moduleText (Result.Ok 64) (Some "ring_imports") importOps)

            match Alex.Patterns.PlatformPatterns.boundaryImportsAt modId graph.Emission.Boundary with
            | Result.Error msg -> Assert.Contains("boundaryImportsIn", msg)
            | Result.Ok _ -> Assert.Fail("Expected boundaryImportsAt to refuse shared-buffer revisions")

            let boundaryScopeGraph =
                { graph with
                    Nodes = graph.Nodes.Remove modId
                    SourceReadings =
                        { graph.SourceReadings with
                            Entries = [ { Focus = modId; Reason = SourceEntryReason.BoundaryScope; Context = [] } ] } }
            let boundaryScopeAcc =
                Alex.Traversal.NanopassArchitecture.executeNanopasses
                    (Alex.Traversal.WitnessRegistry.createRegistry Alex.Target.CPU)
                    boundaryScopeGraph
                    (coeffects 64)
            Assert.True(boundaryScopeAcc.BoundaryScopes.Contains modId)
            Assert.Equal<MLIROp list>(expectedImportOps, List.rev boundaryScopeAcc.AllOps)

        match runBoundaryCallAt mmapCallId graph with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(site, [ { Type = TInt(IntWidth 32) } ], [], [], [ { Type = acqTy } ]) ], TRValue { Type = retTy }), _) ->
            Assert.Equal(mmapCallId, site)
            Assert.Equal(expectedStructTy, acqTy)
            Assert.Equal(expectedStructTy, retTy)
        | Result.Ok _ -> Assert.Fail("Unexpected mmap_ring call witness operations")
        | Result.Error err -> Assert.Fail("Expected mmap_ring call witness to succeed, got: " + err)

        let mkAccWithSlot () =
            let acc = MLIRAccumulator.empty ()
            for (nid, ssa, ty) in
                [ fdParamId, Arg 0, TInt(IntWidth 32)
                  mmapFdArgId, Arg 0, TInt(IntWidth 32)
                  slotBindId, V(2050, 0), expectedStructTy
                  slotRefGetId, V(2050, 0), expectedStructTy
                  slotRefSetId, V(2050, 0), expectedStructTy
                  slotRefMsyncId, V(2050, 0), expectedStructTy
                  slotRefKickId, V(2050, 0), expectedStructTy
                  slotRefMunmapId, V(2050, 0), expectedStructTy
                  val42Id, V(2057, 0), TInt(IntWidth 32) ] do
                MLIRAccumulator.bindNode nid ssa ty acc
            acc

        let nodeAt (g: Revision) (nid: NodeId) =
            Map.tryFind nid g.Nodes
            |> Option.defaultWith (fun () -> failwith "Missing test node")

        let runCallWithSlot site (g: Revision) =
            let acc = mkAccWithSlot ()
            matchAt Alex.Patterns.PlatformPatterns.pBoundaryCall (focus g (nodeAt g site)) 64 acc, acc

        match fst (runCallWithSlot msyncCallId graph) with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(site, [ { SSA = V(2050, 0); Type = argTy } ], [], [], []) ], TRVoid), _) ->
            Assert.Equal(msyncCallId, site)
            Assert.Equal(expectedStructTy, argTy)
        | Result.Ok _ -> Assert.Fail("Unexpected msync_ring call witness operations")
        | Result.Error err -> Assert.Fail("Expected msync_ring call witness to succeed, got: " + err)

        match fst (runCallWithSlot kickCallId graph) with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(site, [ { SSA = V(2050, 0); Type = argTy } ], [], [], []) ], TRVoid), _) ->
            Assert.Equal(kickCallId, site)
            Assert.Equal(expectedStructTy, argTy)
        | Result.Ok _ -> Assert.Fail("Unexpected ring_kick call witness operations")
        | Result.Error err -> Assert.Fail("Expected ring_kick call witness to succeed, got: " + err)

        match fst (runCallWithSlot munmapCallId graph) with
        | Result.Ok(([ MLIROp.BoundaryBufferCall(site, [ { SSA = V(2050, 0); Type = argTy } ], [], [], []) ], TRVoid), _) ->
            Assert.Equal(munmapCallId, site)
            Assert.Equal(expectedStructTy, argTy)
        | Result.Ok _ -> Assert.Fail("Unexpected munmap_ring call witness operations")
        | Result.Error err -> Assert.Fail("Expected munmap_ring call witness to succeed, got: " + err)

        let runRecordNodeAt site (g: Revision) =
            let acc = mkAccWithSlot ()
            let scope = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
            let visited = ref Set.empty
            let targetNode = nodeAt g site
            let ctx : WitnessContext =
                { Coeffects = coeffects 64
                  Accumulator = acc
                  RootAccumulator = acc
                  ScopeContext = scope
                  RootScopeContext = scope
                  Graph = g
                  Zipper = focus g targetNode
                  GlobalVisited = visited
                  TraversalVisited = visited }
            Alex.Witnesses.RecordWitness.nanopass.Witness ctx targetNode, acc

        let assertRecordErrorSubstring (expectedSub: string) (site: NodeId) (g: Revision) =
            let output, acc = runRecordNodeAt site g
            Assert.Empty(output.InlineOps)
            Assert.Empty(output.TopLevelOps)
            Assert.True((MLIRAccumulator.recallNode site acc).IsNone)
            match output.Result with
            | TRError diag -> Assert.Contains(expectedSub, diag.Message)
            | _ -> Assert.Fail("Expected RecordWitness error containing: " + expectedSub)

        let assertCallErrorSubstring (expectedSub: string) (site: NodeId) (g: Revision) =
            let res, acc = runCallWithSlot site g
            Assert.True((MLIRAccumulator.recallNode site acc).IsNone)
            match res with
            | Result.Error msg -> Assert.Contains(expectedSub, msg)
            | Result.Ok _ -> Assert.Fail("Expected pBoundaryCall error containing: " + expectedSub)

        let getOutput, _ = runRecordNodeAt getSeqId graph
        match getOutput.Result with
        | TRError diag -> Assert.Fail("Expected FieldGet on shared buffer to succeed, got: " + diag.Message)
        | _ -> ()
        Assert.False(getOutput.InlineOps |> List.exists (function MLIROp.MemRefOp(MemRefOp.Alloca _) | MLIROp.MemRefOp(MemRefOp.Copy _) -> true | _ -> false))
        match Alex.Dialects.Core.Serialize.moduleToString (Result.Ok 64) "get_view" getOutput.InlineOps with
        | Result.Error err -> Assert.Fail("Expected get_view serialization to succeed: " + err)
        | Result.Ok text ->
            Assert.Contains("memref.view %v2050_0[", text)
            Assert.Contains("memref<8xi8> to memref<1xi32>", text)
            Assert.DoesNotContain("memref.alloca", text)

        let setOutput, _ = runRecordNodeAt setPayloadId graph
        match setOutput.Result with
        | TRError diag -> Assert.Fail("Expected FieldSet on shared buffer to succeed, got: " + diag.Message)
        | _ -> ()
        Assert.False(setOutput.InlineOps |> List.exists (function MLIROp.MemRefOp(MemRefOp.Alloca _) | MLIROp.MemRefOp(MemRefOp.Copy _) -> true | _ -> false))
        match Alex.Dialects.Core.Serialize.moduleToString (Result.Ok 64) "set_view" setOutput.InlineOps with
        | Result.Error err -> Assert.Fail("Expected set_view serialization to succeed: " + err)
        | Result.Ok text ->
            Assert.Contains("memref.view %v2050_0[", text)
            Assert.Contains("memref<8xi8> to memref<1xi32>", text)
            Assert.DoesNotContain("memref.alloca", text)

        // Mutant 1: Non-zero copy count (Copies = 1) must be refused fail-closed
        let copiesMutantGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferViewUses = Map.ofList [ getSeqId, { viewUse with Copies = 1 } ] } } }
        match Alex.Patterns.PlatformPatterns.boundaryImportsIn modId copiesMutantGraph with
        | Result.Error msg -> Assert.Contains("Copies", msg)
        | Result.Ok _ -> Assert.Fail("Expected boundaryImportsIn to refuse Copies = 1")
        assertCallErrorSubstring "Copies" mmapCallId copiesMutantGraph
        assertRecordErrorSubstring "Copies" getSeqId copiesMutantGraph

        // Mutant 2: Missing FS9223 exclusivity obligation from CurrentClaims must be refused fail-closed
        let missingObGraph =
            { graph with
                Nodes = graph.Nodes.Remove obExclusivityId
                CurrentClaims = graph.CurrentClaims.Remove obExclusivityId }
        match Alex.Patterns.PlatformPatterns.boundaryImportsIn modId missingObGraph with
        | Result.Error msg -> Assert.Contains("obligations", msg)
        | Result.Ok _ -> Assert.Fail("Expected boundaryImportsIn to refuse missing obligation")
        assertCallErrorSubstring "obligations" mmapCallId missingObGraph
        assertRecordErrorSubstring "obligations" setPayloadId missingObGraph

        // Mutant 3: Swapped/wrong-placement obligation form in CurrentClaims must be refused fail-closed
        let wrongPlacementBareOb =
            { layoutBare with
                Source = "platform:test-ring-platform:shared_buffer:other_placement"
                Form = { layoutBare.Form with A = 3L } }
        let wrongObInfo = mkOb wrongPlacementBareOb
        let swappedObGraph =
            { graph with
                Obligations = [ wrongObInfo; obExtent; obSpace; obLifetime; obExclusivity ]
                CurrentClaims = graph.CurrentClaims.Add(obLayoutId, wrongObInfo) }
        assertCallErrorSubstring "obligations" mmapCallId swappedObGraph
        assertRecordErrorSubstring "obligations" getSeqId swappedObGraph

        // Mutant 4: Write projection on ReadOnly shared-buffer placement must be refused fail-closed
        let readOnlyPlacement =
            { placement with Space = { space with Access = BAREWire.Platform.Access.ReadOnly } }
        let readOnlyMutantGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferPlacements = Map.ofList [ plId, readOnlyPlacement ] } } }
        assertRecordErrorSubstring "ReadOnly" setPayloadId readOnlyMutantGraph

        // Mutant 5: Read projection on WriteOnly shared-buffer placement must be refused fail-closed
        let writeOnlyPlacement =
            { placement with Space = { space with Access = BAREWire.Platform.Access.WriteOnly } }
        let writeOnlyMutantGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferPlacements = Map.ofList [ plId, writeOnlyPlacement ] } } }
        assertRecordErrorSubstring "WriteOnly" getSeqId writeOnlyMutantGraph

        // Mutant 6: Write projection on a field-level ReadOnly field inside a ReadWrite placement must be refused
        let f0, f1 =
            match Array.toList structLayout.Layout.Fields with
            | [ a; b ] -> a, b
            | _ -> failwith "Unexpected structLayout field count"
        let fieldReadOnlyStructLayout =
            { structLayout with
                Layout =
                    { structLayout.Layout with
                        Fields =
                            [| f0
                               { f1 with Access = BAREWire.Hardware.AccessKind.ReadOnly } |] } }
        let fieldReadOnlyBarePlacement = { barePlacement with StructLayout = fieldReadOnlyStructLayout }
        let fieldRoObs = BAREWire.Platform.Obligations.sharedBufferObligations desc [| fieldReadOnlyBarePlacement |]
        let fieldRoExclInfo =
            match Array.toList fieldRoObs with
            | [ _; _; _; exclOb; _ ] -> mkOb exclOb
            | _ -> failwith "Unexpected fieldRoObs count"
        let fieldReadOnlyPlacement =
            { placement with
                Placement = fieldReadOnlyBarePlacement
                DeclarationFacts = makePlacementDeclFacts 2070 fieldReadOnlyBarePlacement regionDesc space bufferSchema }
        let fieldReadOnlyGraph =
            { graph with
                Nodes = graph.Nodes.Add(obExclusivityId, mkNode obExclusivityId unitType (SemanticKind.Obligation fieldRoExclInfo) [])
                Obligations = [ obLayout; obExtent; obSpace; obLifetime; fieldRoExclInfo ]
                CurrentClaims = graph.CurrentClaims.Add(obExclusivityId, fieldRoExclInfo)
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferPlacements = Map.ofList [ plId, fieldReadOnlyPlacement ] } } }
        assertRecordErrorSubstring "violates ReadOnly permission" setPayloadId fieldReadOnlyGraph

        // Mutant 7: Lifetime order violation (ReleaseOrder <= WriteProjectionOrders) must be refused fail-closed
        let badOrderGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferViewUses = Map.ofList [ getSeqId, { viewUse with ReleaseOrder = Some 2 } ] } } }
        assertCallErrorSubstring "order domination" munmapCallId badOrderGraph

        // Mutant 8: Missing ReleaseOrder / RegionReleaseCall on LeakedAtExit = false must be refused fail-closed
        let missingReleaseGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferViewUses =
                                    Map.ofList [ getSeqId, { viewUse with RegionReleaseCall = None; ReleaseOrder = None } ] } } }
        assertCallErrorSubstring "order domination" mmapCallId missingReleaseGraph

        // Mutant 9: Unsynchronized foreign use call after write projection must be refused fail-closed
        let unsyncGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferViewUses = Map.ofList [ getSeqId, { viewUse with SyncCalls = []; SyncOrders = [] } ] } } }
        assertCallErrorSubstring "unbracketed foreign use" kickCallId unsyncGraph

        // Mutant 10: Unregistered projection missing from ViewProjections must be refused fail-closed
        let unregisteredProjGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                SharedBufferViewUses =
                                    Map.ofList [ getSeqId, { viewUse with ViewProjections = []; ProjectionOrders = [] } ] } } }
        assertRecordErrorSubstring "ViewProjections" getSeqId unregisteredProjGraph

        // Mutant 11: Unlisted projection through a 2-hop alias chain must be refused fail-closed
        let aliasBindId = id 2085
        let aliasRefId = id 2086
        let unlistedGetId = id 2087
        let twoHopGraph =
            { graph with
                Nodes =
                    graph.Nodes
                        .Add(aliasBindId, mkNodeWithParent aliasBindId ringSlotType (SemanticKind.Binding("slotAlias", false, false, None)) [ slotRefGetId ] (Some bodySeqId))
                        .Add(aliasRefId, mkNodeWithParent aliasRefId ringSlotType (SemanticKind.VarRef("slotAlias", Some aliasBindId)) [] (Some unlistedGetId))
                        .Add(unlistedGetId, mkNodeWithParent unlistedGetId intType (SemanticKind.FieldGet(aliasRefId, "Seq")) [ aliasRefId ] (Some bodySeqId))
                Emission =
                    { graph.Emission with
                        Callable =
                            { graph.Emission.Callable with
                                AliasTargets =
                                    graph.Emission.Callable.AliasTargets
                                        .Add(aliasBindId, slotRefGetId)
                                        .Add(aliasRefId, aliasBindId)
                                        .Add(unlistedGetId, unlistedGetId) }
                        Numeric =
                            { graph.Emission.Numeric with
                                SourceTypes =
                                    graph.Emission.Numeric.SourceTypes
                                        .Add(aliasBindId, ringSlotType)
                                        .Add(aliasRefId, ringSlotType)
                                OccurrenceRepresentations =
                                    graph.Emission.Numeric.OccurrenceRepresentations
                                        .Add(aliasBindId, Result.Ok ringSlotRep)
                                        .Add(aliasRefId, Result.Ok ringSlotRep)
                                        .Add(unlistedGetId, Result.Ok i32Rep) } } }
            |> declareTraversalReadings
        let accTwoHop = mkAccWithSlot ()
        MLIRAccumulator.bindNode aliasBindId (V(2085, 0)) expectedStructTy accTwoHop
        MLIRAccumulator.bindNode aliasRefId (V(2086, 0)) expectedStructTy accTwoHop
        let scopeTwoHop = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
        let visitedTwoHop = ref Set.empty
        let unlistedGetTargetNode = nodeAt twoHopGraph unlistedGetId
        let ctxTwoHop : WitnessContext =
            { Coeffects = coeffects 64
              Accumulator = accTwoHop
              RootAccumulator = accTwoHop
              ScopeContext = scopeTwoHop
              RootScopeContext = scopeTwoHop
              Graph = twoHopGraph
              Zipper = focus twoHopGraph unlistedGetTargetNode
              GlobalVisited = visitedTwoHop
              TraversalVisited = visitedTwoHop }
        let outTwoHop = Alex.Witnesses.RecordWitness.nanopass.Witness ctxTwoHop unlistedGetTargetNode
        Assert.Empty(outTwoHop.InlineOps)
        Assert.Empty(outTwoHop.TopLevelOps)
        Assert.Empty(Alex.Traversal.ScopeContext.ScopeContext.getOps (!scopeTwoHop))
        Assert.Equal(None, MLIRAccumulator.recallNode unlistedGetId accTwoHop)
        match outTwoHop.Result with
        | TRError diag -> Assert.Contains("Shared-buffer read projection at node", diag.Message)
        | _ -> Assert.Fail("Expected 2-hop unlisted projection on shared buffer to be refused")

        // Mutant 12: Shared-buffer call tampered with call.Resource = Some ... must be refused fail-closed
        let tamperedResourceCall =
            { msyncCall with
                Resource =
                    Some(
                        BoundaryResourceUse.ReleaseOwned
                            { Declaration = plId
                              Acquisition = mmapCallId
                              Cleanup = obLifetimeId }) }
        let tamperedResourceGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                Calls = graph.Emission.Boundary.Calls.Add(msyncCallId, tamperedResourceCall) } } }
        assertCallErrorSubstring "cannot carry resource lifetime adaptation" msyncCallId tamperedResourceGraph

        // Mutant 13: RecordExpr copy-with from a zero-copy shared-buffer origin must be refused fail-closed
        let copyWithId = id 2090
        let copyWithNode =
            mkNode copyWithId ringSlotType (SemanticKind.RecordExpr([ "Payload", val42Id ], Some slotRefGetId)) [ slotRefGetId; val42Id ]
        let copyWithGraph =
            { graph with
                Nodes = graph.Nodes.Add(copyWithId, copyWithNode)
                Codata = { graph.Codata with Escapes = Map.ofList [ copyWithId, EscapeKind.StackScoped ] }
                Emission =
                    { graph.Emission with
                        Callable = { graph.Emission.Callable with AliasTargets = graph.Emission.Callable.AliasTargets.Add(copyWithId, copyWithId) }
                        Numeric =
                            { graph.Emission.Numeric with
                                SourceTypes = graph.Emission.Numeric.SourceTypes.Add(copyWithId, ringSlotType)
                                OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations.Add(copyWithId, Result.Ok ringSlotRep) } } }
            |> declareTraversalReadings
        assertRecordErrorSubstring "Shared-buffer view cannot be copied via record copy-and-update" copyWithId copyWithGraph

        // Mutant 14: TupleExpr capturing a zero-copy shared-buffer origin must be refused fail-closed
        let tupleCaptureId = id 2091
        let tupleType =
            TypeIdentity.Tuple(false, [ ringSlotType; intType ])
        let tupleRep =
            ValueRepresentation.Record(
                [ "Item1", ringSlotRep; "Item2", i32Rep ],
                Some([ 0; 8 ], 16, 4))
        let tupleCaptureNode =
            mkNode tupleCaptureId tupleType (SemanticKind.TupleExpr [ slotRefGetId; val42Id ]) [ slotRefGetId; val42Id ]
        let tupleCaptureGraph =
            { graph with
                Nodes = graph.Nodes.Add(tupleCaptureId, tupleCaptureNode)
                Emission =
                    { graph.Emission with
                        Numeric =
                            { graph.Emission.Numeric with
                                TypeRepresentations = graph.Emission.Numeric.TypeRepresentations.Add(tupleType, Result.Ok tupleRep)
                                OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations.Add(tupleCaptureId, Result.Ok tupleRep) } } }
            |> declareTraversalReadings
        assertRecordErrorSubstring "Shared-buffer view cannot be captured as a tuple element" tupleCaptureId tupleCaptureGraph

        // Mutant 15: Mutable binding capturing a zero-copy shared-buffer origin must be refused fail-closed
        let mutBindId = id 2092
        let mutBindNode =
            mkNode mutBindId ringSlotType (SemanticKind.Binding("mutSlot", true, false, None)) [ slotRefGetId ]
        let mutBindGraph =
            { graph with
                Nodes = graph.Nodes.Add(mutBindId, mutBindNode)
                Emission =
                    { graph.Emission with
                        Numeric =
                            { graph.Emission.Numeric with
                                SourceTypes = graph.Emission.Numeric.SourceTypes.Add(mutBindId, ringSlotType)
                                OccurrenceRepresentations = graph.Emission.Numeric.OccurrenceRepresentations.Add(mutBindId, Result.Ok ringSlotRep) } } }
            |> declareTraversalReadings
        let accMut = mkAccWithSlot ()
        let scopeMut = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
        let visitedMut = ref Set.empty
        let mutBindTargetNode = nodeAt mutBindGraph mutBindId
        let ctxMut : WitnessContext =
            { Coeffects = coeffects 64
              Accumulator = accMut
              RootAccumulator = accMut
              ScopeContext = scopeMut
              RootScopeContext = scopeMut
              Graph = mutBindGraph
              Zipper = focus mutBindGraph mutBindTargetNode
              GlobalVisited = visitedMut
              TraversalVisited = visitedMut }
        let outMut = Alex.Witnesses.BindingWitness.nanopass.Witness ctxMut mutBindTargetNode
        Assert.Empty(outMut.InlineOps)
        Assert.Empty(outMut.TopLevelOps)
        Assert.Empty(Alex.Traversal.ScopeContext.ScopeContext.getOps (!scopeMut))
        Assert.Equal(None, MLIRAccumulator.recallNode mutBindId accMut)
        match outMut.Result with
        | TRError diag -> Assert.Contains("Shared-buffer view cannot be bound to a mutable cell", diag.Message)
        | _ -> Assert.Fail("Expected mutable binding of shared-buffer view to be refused")

        // Mutant 16: FnPtr.ofExtern / nativeEntrySlotType and pImportedFunctionAddress on a shared-buffer import must be refused fail-closed
        Assert.True(Alex.Dialects.Core.Types.BoundaryAbi.isSharedBufferImport graph mmapImport)
        Assert.True(Alex.Dialects.Core.Types.BoundaryAbi.isSharedBufferImport graph msyncImport)
        Assert.True(Alex.Dialects.Core.Types.BoundaryAbi.isSharedBufferImport graph kickImport)
        Assert.True(Alex.Dialects.Core.Types.BoundaryAbi.isSharedBufferImport graph munmapImport)
        let formationId = id 2093
        let fnPtrCalleeId = id 2094
        let loadingId = id 2095
        let fnPtrCtor : ConstructorIdentity =
            { Declaration = { Module = []; Name = "FnPtr" }
              Parameters = [ TypeParamKind.Type ]
              NativeKind = Some NTUKind.NTUfnptr }
        let msyncFnType = functionFrom ringSlotType unitType
        let msyncFnPtrType = TypeIdentity.Application(fnPtrCtor, [ msyncFnType ])
        let mmapFnType = functionFrom intType ringSlotType
        let mmapFnPtrType = TypeIdentity.Application(fnPtrCtor, [ mmapFnType ])
        let linkContract : BAREWire.Platform.ProcessLinkContract =
            { Identity = "ring-process-link"
              Version = "1"
              Source = "test"
              Library = "ring"
              Runtime = "libc"
              Os = "linux"
              Arch = "x86_64"
              LoadAt = "ProcessStartup"
              LiveUntil = "ProcessTermination"
              Unloading = "Forbidden"
              ExportedLibrary = "Forbidden" }
        let loadingRow : BoundaryLoading =
            { Identity = loadingId
              Binding = loadingId
              Platform = loadingId
              Core = loadingId
              Selector = "linux-x86_64"
              Contract = linkContract
              DeclarationFacts = Map.empty
              Participants = Set.singleton loadingId }
        let entryRow : BoundaryEntry =
            { Formation = formationId
              Declaration = msyncDeclId
              Import = msyncDescId
              Operand = msyncCalleeId
              Loading = loadingId
              SourceType = msyncFnPtrType
              Transport = Set.ofList [ formationId; msyncCalleeId; msyncDeclId ]
              Participants = Set.ofList [ formationId; msyncCalleeId; msyncDeclId; loadingId ] }
        let storageEntry : ProgramStorageEntry =
            { Identity = ProgramStorageIdentity.BindingSlot formationId
              SourceType = msyncFnPtrType
              Shape = ProgramStorageShape.NativeEntry formationId
              Bytes = 8
              Alignment = 8
              SpaceNode = spaceNodeId
              Space = space
              Participants = Set.singleton formationId }
        let fnPtrGraph =
            { graph with
                Nodes =
                    graph.Nodes
                        .Add(fnPtrCalleeId, mkNode fnPtrCalleeId unitType (SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "ofExtern"; Category = IntrinsicCategory.Memory; FullName = "FnPtr.ofExtern" }) [])
                        .Add(formationId, mkNode formationId msyncFnPtrType (SemanticKind.Application(fnPtrCalleeId, [ msyncCalleeId ])) [ fnPtrCalleeId; msyncCalleeId ])
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                Loading = Some loadingRow
                                Entries = Map.ofList [ formationId, entryRow ] } } }
            |> declareTraversalReadings
        match Alex.CodeGeneration.TypeMapping.nativeEntrySlotType fnPtrGraph storageEntry with
        | Result.Error msg -> Assert.Contains("Resource-bearing imports require a direct source call", msg)
        | Result.Ok _ -> Assert.Fail("Expected nativeEntrySlotType to refuse shared-buffer import")
        let accFnPtr = mkAccWithSlot ()
        let fnPtrRes =
            matchAt
                (Alex.Patterns.PlatformPatterns.pImportedFunctionAddress formationId)
                (focus fnPtrGraph (nodeAt fnPtrGraph formationId))
                64
                accFnPtr
        Assert.Empty(accFnPtr.AllOps)
        Assert.Equal(None, MLIRAccumulator.recallNode formationId accFnPtr)
        match fnPtrRes with
        | Result.Error msg -> Assert.Contains("Resource-bearing imports require a direct source call", msg)
        | Result.Ok _ -> Assert.Fail("Expected pImportedFunctionAddress to refuse shared-buffer import")

        let mmapEntryRow : BoundaryEntry =
            { Formation = formationId
              Declaration = mmapDeclId
              Import = mmapDescId
              Operand = mmapCalleeId
              Loading = loadingId
              SourceType = mmapFnPtrType
              Transport = Set.ofList [ formationId; mmapCalleeId; mmapDeclId ]
              Participants = Set.ofList [ formationId; mmapCalleeId; mmapDeclId; loadingId ] }
        let mmapStorageEntry : ProgramStorageEntry =
            { storageEntry with SourceType = mmapFnPtrType }
        let mmapFnPtrGraph =
            { graph with
                Nodes =
                    graph.Nodes
                        .Add(fnPtrCalleeId, mkNode fnPtrCalleeId unitType (SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "ofExtern"; Category = IntrinsicCategory.Memory; FullName = "FnPtr.ofExtern" }) [])
                        .Add(formationId, mkNode formationId mmapFnPtrType (SemanticKind.Application(fnPtrCalleeId, [ mmapCalleeId ])) [ fnPtrCalleeId; mmapCalleeId ])
                Emission =
                    { graph.Emission with
                        Boundary =
                            { graph.Emission.Boundary with
                                Loading = Some loadingRow
                                Entries = Map.ofList [ formationId, mmapEntryRow ] } } }
            |> declareTraversalReadings
        match Alex.CodeGeneration.TypeMapping.nativeEntrySlotType mmapFnPtrGraph mmapStorageEntry with
        | Result.Error msg -> Assert.Contains("Resource-bearing imports require a direct source call", msg)
        | Result.Ok _ -> Assert.Fail("Expected nativeEntrySlotType to refuse shared-buffer acquisition import (mmapImport)")
        let accMmapFnPtr = mkAccWithSlot ()
        let mmapFnPtrRes =
            matchAt
                (Alex.Patterns.PlatformPatterns.pImportedFunctionAddress formationId)
                (focus mmapFnPtrGraph (nodeAt mmapFnPtrGraph formationId))
                64
                accMmapFnPtr
        Assert.Empty(accMmapFnPtr.AllOps)
        Assert.Equal(None, MLIRAccumulator.recallNode formationId accMmapFnPtr)
        match mmapFnPtrRes with
        | Result.Error msg -> Assert.Contains("Resource-bearing imports require a direct source call", msg)
        | Result.Ok _ -> Assert.Fail("Expected pImportedFunctionAddress to refuse shared-buffer acquisition import (mmapImport)")

        // Mutant 17 (GA-A5-R2-1): Unlisted foreign import taking RingSlot must be refused by boundaryImportsIn,
        // while a 2-placement RingSlot graph with distinct RegionDescriptor role bindings succeeds
        let unlistedDeclId = id 2096
        let unlistedDescId = id 2097
        let unlistedFormalId = id 2098
        let unlistedImport = mkSlotImport unlistedDescId unlistedDeclId unlistedFormalId "unlistedFn" "unlisted_c"
        let unlistedImportGraph =
            { graph with
                Emission =
                    { graph.Emission with
                        Callable =
                            { graph.Emission.Callable with
                                Symbols =
                                    graph.Emission.Callable.Symbols.Add(
                                        unlistedDeclId,
                                        CallableSymbolName.ModuleBinding("RingMod", "unlistedFn")) }
                        Boundary =
                            { graph.Emission.Boundary with
                                ByScope =
                                    Map.ofList
                                        [ modId, [ mmapDescId; msyncDescId; kickDescId; munmapDescId; unlistedDescId ] ]
                                Imports = graph.Emission.Boundary.Imports.Add(unlistedDescId, unlistedImport) } } }
        match Alex.Patterns.PlatformPatterns.boundaryImportsIn modId unlistedImportGraph with
        | Result.Error msg -> Assert.Contains("without a valid non-null shared-buffer consumer role", msg)
        | Result.Ok _ -> Assert.Fail("Expected boundaryImportsIn to refuse unlisted foreign import taking RingSlot")

        let extraHandleFormalId = id 2099
        let unlistedDualHandleImport : BoundaryImport =
            { unlistedImport with
                Parameters =
                    [ extraHandleFormalId, BoundaryScalar.ResourceHandle(extraHandleFormalId, false)
                      unlistedFormalId, BoundaryScalar.ResourceHandle(unlistedFormalId, false) ]
                Participants = Set.add extraHandleFormalId unlistedImport.Participants
                SourceTypes = unlistedImport.SourceTypes.Add(extraHandleFormalId, intType)
                DeclarationFacts =
                    unlistedImport.DeclarationFacts.Add(
                        extraHandleFormalId,
                        { emptyFact "binding" with SourceType = intType }) }
        let unlistedDualHandleGraph =
            { unlistedImportGraph with
                Emission =
                    { unlistedImportGraph.Emission with
                        Boundary =
                            { unlistedImportGraph.Emission.Boundary with
                                Imports = graph.Emission.Boundary.Imports.Add(unlistedDescId, unlistedDualHandleImport) } } }
        match Alex.Patterns.PlatformPatterns.boundaryImportsIn modId unlistedDualHandleGraph with
        | Result.Error msg -> Assert.Contains("without a valid non-null shared-buffer consumer role", msg)
        | Result.Ok _ -> Assert.Fail("Expected boundaryImportsIn to refuse unlisted dual-handle import taking (h: Handle, slot: RingSlot)")

        let pl2Id = id 2200
        let pl2DeclId = id 2201
        let space2NodeId = id 2202
        let buf2NodeId = id 2203
        let space2DescNodeId = id 2204
        let struct2DescNodeId = id 2205
        let view2DescNodeId = id 2206
        let region2DescNodeId = id 2207
        let ob2LayoutId = id 2210
        let ob2ExtentId = id 2211
        let ob2LifetimeId = id 2212
        let ob2ExclusivityId = id 2213
        let mmap2DeclId = id 2220
        let mmap2DescId = id 2221
        let mmap2FdFormal = id 2222
        let msync2DeclId = id 2230
        let msync2DescId = id 2231
        let msync2SlotFormal = id 2232
        let kick2DeclId = id 2240
        let kick2DescId = id 2241
        let kick2SlotFormal = id 2242
        let munmap2DeclId = id 2250
        let munmap2DescId = id 2251
        let munmap2SlotFormal = id 2252
        let barePlacement2 =
            { barePlacement with
                Name = "ring_slot_aux"
                SpaceOffset = 64L }
        let regionDesc2 : BAREWire.Descriptors.SharedBufferRegionDescriptor =
            { Placement = "ring_slot_aux"
              Acquire = "RingMod.mmapRingAux"
              Release = Some "RingMod.munmapRingAux"
              Sync = [| "RingMod.msyncRingAux" |]
              ForeignUses = [| "RingMod.ringKickAux" |] }
        let rawObs2 = BAREWire.Platform.Obligations.sharedBufferObligations desc [| barePlacement; barePlacement2 |]
        let ob1Extent, ob1Layout, ob1Lifetime, ob1Exclusivity, ob2Extent, ob2Layout, ob2Lifetime, ob2Exclusivity, obBothSpace =
            match Array.toList rawObs2 with
            | [ r0; r1; r2; r3; r4; r5; r6; r7; r8 ] ->
                mkOb r0, mkOb r1, mkOb r2, mkOb r3, mkOb r4, mkOb r5, mkOb r6, mkOb r7, mkOb r8
            | _ -> failwith "Unexpected 2-placement shared-buffer obligation count"
        let placement1ForTwo =
            { placement with
                Obligations = [ obLayoutId; obExtentId; obSpaceId; obLifetimeId; obExclusivityId ] }
        let placement2Participants =
            [ 2200 .. 2207 ]
            |> List.mapi (fun idx nid -> { Role = ParticipantRole.Site; Node = NodeId nid; Ordinal = idx; Group = pl2Id })
        let placement2 : BoundarySharedBufferPlacementDeclaration =
            { Identity = pl2Id
              Declaration = pl2DeclId
              SpaceNode = space2NodeId
              BufferSchemaNode = buf2NodeId
              SpaceDescriptorNode = space2DescNodeId
              StructDescriptorNode = struct2DescNodeId
              ViewDescriptorNode = view2DescNodeId
              RegionDescriptorNode = region2DescNodeId
              Placement = barePlacement2
              RegionDescriptor = regionDesc2
              Space = space
              BufferSchema = bufferSchema
              PlatformEndianness = "little"
              Obligations = [ ob2LayoutId; ob2ExtentId; obSpaceId; ob2LifetimeId; ob2ExclusivityId ]
              DeclarationFacts = makePlacementDeclFacts 2200 barePlacement2 regionDesc2 space bufferSchema
              Participants = ParticipantEvidence.Established placement2Participants }
        let mmap2Import : BoundaryImport =
            { Identity = mmap2DescId; Binding = mmap2DeclId; Scope = modId
              Library = "ring"; Symbol = "mmap_ring_aux"; CallingConvention = "CDecl"
              FixedSentinels = []; DeclarationPath = [ modId; mmap2DeclId ]
              Parameters = [ mmap2FdFormal, BoundaryScalar.Integer(32, true) ]
              Result = Some(BoundaryScalar.Integer(64, false))
              Participants = Set.ofList [ modId; mmap2DeclId; mmap2DescId; mmap2FdFormal ]
              SourceTypes = Map.ofList [ mmap2DeclId, functionFrom intType ringSlotType; mmap2FdFormal, intType ]
              DeclarationFacts =
                Map.ofList
                    [ mmap2DeclId, mkImportBindingFact "mmapRingAux" (functionFrom intType ringSlotType)
                      mmap2FdFormal, { emptyFact "binding" with SourceType = intType } ] }
        let msync2Import = mkSlotImport msync2DescId msync2DeclId msync2SlotFormal "msyncRingAux" "msync_ring_aux"
        let kick2Import = mkSlotImport kick2DescId kick2DeclId kick2SlotFormal "ringKickAux" "ring_kick_aux"
        let munmap2Import = mkSlotImport munmap2DescId munmap2DeclId munmap2SlotFormal "munmapRingAux" "munmap_ring_aux"
        let platformPremise2 =
            { platformPremise with SharedBufferRegions = [ regionDesc; regionDesc2 ] }
        let boundaryDomain2 =
            { boundaryDomain with Platform = Some platformPremise2 }
        let domainEdge2 : Hyperedge =
            { domainEdge with Role = EdgeRole.BoundaryDomain boundaryDomain2 }
        let twoPlacementGraph =
            { graph with
                Edges = [ domainEdge2 ]
                Nodes =
                    graph.Nodes
                        .Add(obLayoutId, mkNode obLayoutId unitType (SemanticKind.Obligation ob1Layout) [])
                        .Add(obExtentId, mkNode obExtentId unitType (SemanticKind.Obligation ob1Extent) [])
                        .Add(obSpaceId, mkNode obSpaceId unitType (SemanticKind.Obligation obBothSpace) [])
                        .Add(obLifetimeId, mkNode obLifetimeId unitType (SemanticKind.Obligation ob1Lifetime) [])
                        .Add(obExclusivityId, mkNode obExclusivityId unitType (SemanticKind.Obligation ob1Exclusivity) [])
                        .Add(ob2LayoutId, mkNode ob2LayoutId unitType (SemanticKind.Obligation ob2Layout) [])
                        .Add(ob2ExtentId, mkNode ob2ExtentId unitType (SemanticKind.Obligation ob2Extent) [])
                        .Add(ob2LifetimeId, mkNode ob2LifetimeId unitType (SemanticKind.Obligation ob2Lifetime) [])
                        .Add(ob2ExclusivityId, mkNode ob2ExclusivityId unitType (SemanticKind.Obligation ob2Exclusivity) [])
                Obligations =
                    [ ob1Layout; ob1Extent; obBothSpace; ob1Lifetime; ob1Exclusivity
                      ob2Layout; ob2Extent; ob2Lifetime; ob2Exclusivity ]
                CurrentClaims =
                    Map.ofList
                        [ obLayoutId, ob1Layout
                          obExtentId, ob1Extent
                          obSpaceId, obBothSpace
                          obLifetimeId, ob1Lifetime
                          obExclusivityId, ob1Exclusivity
                          ob2LayoutId, ob2Layout
                          ob2ExtentId, ob2Extent
                          ob2LifetimeId, ob2Lifetime
                          ob2ExclusivityId, ob2Exclusivity ]
                Emission =
                    { graph.Emission with
                        Callable =
                            { graph.Emission.Callable with
                                Symbols =
                                    graph.Emission.Callable.Symbols
                                        .Add(mmap2DeclId, CallableSymbolName.ModuleBinding("RingMod", "mmapRingAux"))
                                        .Add(msync2DeclId, CallableSymbolName.ModuleBinding("RingMod", "msyncRingAux"))
                                        .Add(kick2DeclId, CallableSymbolName.ModuleBinding("RingMod", "ringKickAux"))
                                        .Add(munmap2DeclId, CallableSymbolName.ModuleBinding("RingMod", "munmapRingAux")) }
                        Boundary =
                            { graph.Emission.Boundary with
                                ByScope =
                                    Map.ofList
                                        [ modId,
                                          [ mmapDescId; msyncDescId; kickDescId; munmapDescId
                                            mmap2DescId; msync2DescId; kick2DescId; munmap2DescId ] ]
                                Imports =
                                    graph.Emission.Boundary.Imports
                                        .Add(mmap2DescId, mmap2Import)
                                        .Add(msync2DescId, msync2Import)
                                        .Add(kick2DescId, kick2Import)
                                        .Add(munmap2DescId, munmap2Import)
                                SharedBufferPlacements =
                                    Map.ofList
                                        [ plId, placement1ForTwo
                                          pl2Id, placement2 ] } } }
            |> declareTraversalReadings
        match Alex.Patterns.PlatformPatterns.boundaryImportsIn modId twoPlacementGraph with
        | Result.Error err -> Assert.Fail("Expected 2-placement RingSlot boundaryImportsIn to succeed, got: " + err)
        | Result.Ok twoPlacementOps ->
            Assert.Equal(8, twoPlacementOps.Length)
            Assert.Contains(
                MLIROp.FuncOp(FuncOp.BoundaryFuncDecl(mmap2Import, [ TInt(IntWidth 32) ], [ expectedStructTy ])),
                twoPlacementOps)

        let wrongPlacementRoleCall =
            mkSlotCall msyncCallId msync2DescId msyncCalleeId slotRefMsyncId msync2SlotFormal
        let wrongPlacementRoleGraph =
            { twoPlacementGraph with
                Emission =
                    { twoPlacementGraph.Emission with
                        Boundary =
                            { twoPlacementGraph.Emission.Boundary with
                                Calls = twoPlacementGraph.Emission.Boundary.Calls.Add(msyncCallId, wrongPlacementRoleCall) } } }
        match Alex.Patterns.PlatformPatterns.boundaryImportsIn modId wrongPlacementRoleGraph with
        | Result.Error msg -> Assert.Contains("RegionDescriptor", msg)
        | Result.Ok _ -> Assert.Fail("Expected boundaryImportsIn to refuse msync2Import called in placement 1's SyncCalls")
        assertCallErrorSubstring "RegionDescriptor" msyncCallId wrongPlacementRoleGraph

        // Mutant 18 (GA-A5-R2-2): Ordinary stack record with identical ValueRepresentation but distinct nominal TypeIdentity
        // must succeed in FieldGet, FieldSet, and RecordExpr without false-positive shared-buffer refusal
        let ordinaryPairType =
            TypeIdentity.Application(
                { Declaration = { Module = [ "RingMod" ]; Name = "OrdinaryPair" }
                  Parameters = []
                  NativeKind = None },
                [])
        let ordOrigId = id 2350
        let ordGetId = id 2351
        let ordSetId = id 2352
        let ordRecId = id 2353
        let ordinaryGraph =
            { graph with
                Nodes =
                    graph.Nodes
                        .Add(ordOrigId, mkNode ordOrigId ordinaryPairType (SemanticKind.PatternBinding "ord") [])
                        .Add(ordGetId, mkNode ordGetId intType (SemanticKind.FieldGet(ordOrigId, "Seq")) [ ordOrigId ])
                        .Add(ordSetId, mkNode ordSetId unitType (SemanticKind.FieldSet(ordOrigId, "Payload", val42Id)) [ ordOrigId; val42Id ])
                        .Add(ordRecId, mkNode ordRecId ordinaryPairType (SemanticKind.RecordExpr([ "Seq", val42Id; "Payload", val42Id ], None)) [ val42Id; val42Id ])
                Codata = { graph.Codata with Escapes = Map.ofList [ ordRecId, EscapeKind.StackScoped ] }
                Emission =
                    { graph.Emission with
                        Callable =
                            { graph.Emission.Callable with
                                AliasTargets =
                                    graph.Emission.Callable.AliasTargets
                                        .Add(ordOrigId, ordOrigId)
                                        .Add(ordGetId, ordGetId)
                                        .Add(ordSetId, ordSetId)
                                        .Add(ordRecId, ordRecId) }
                        Numeric =
                            { graph.Emission.Numeric with
                                SourceTypes =
                                    graph.Emission.Numeric.SourceTypes
                                        .Add(ordOrigId, ordinaryPairType)
                                        .Add(ordGetId, intType)
                                        .Add(ordSetId, unitType)
                                        .Add(ordRecId, ordinaryPairType)
                                Layouts = graph.Emission.Numeric.Layouts.Add(ordinaryPairType, ringSlotLayout)
                                TypeRepresentations = graph.Emission.Numeric.TypeRepresentations.Add(ordinaryPairType, Result.Ok ringSlotRep)
                                OccurrenceRepresentations =
                                    graph.Emission.Numeric.OccurrenceRepresentations
                                        .Add(ordOrigId, Result.Ok ringSlotRep)
                                        .Add(ordGetId, Result.Ok i32Rep)
                                        .Add(ordSetId, Result.Ok unitRep)
                                        .Add(ordRecId, Result.Ok ringSlotRep) } } }
            |> declareTraversalReadings
        Assert.False(Alex.Dialects.Core.Types.BoundaryAbi.isSharedBufferOrigin ordinaryGraph ordOrigId)
        let runOrdinaryRecordAt site =
            let accOrd = mkAccWithSlot ()
            MLIRAccumulator.bindNode ordOrigId (V(2350, 0)) expectedStructTy accOrd
            let scopeOrd = ref (Alex.Traversal.ScopeContext.ScopeContext.root ())
            let visitedOrd = ref Set.empty
            let ordTargetNode = nodeAt ordinaryGraph site
            let ctxOrd : WitnessContext =
                { Coeffects = coeffects 64
                  Accumulator = accOrd
                  RootAccumulator = accOrd
                  ScopeContext = scopeOrd
                  RootScopeContext = scopeOrd
                  Graph = ordinaryGraph
                  Zipper = focus ordinaryGraph ordTargetNode
                  GlobalVisited = visitedOrd
                  TraversalVisited = visitedOrd }
            Alex.Witnesses.RecordWitness.nanopass.Witness ctxOrd ordTargetNode
        let ordGetOut = runOrdinaryRecordAt ordGetId
        match ordGetOut.Result with
        | TRError diag -> Assert.Fail("Expected ordinary record FieldGet to succeed, got: " + diag.Message)
        | _ -> Assert.NotEmpty(ordGetOut.InlineOps)
        let ordSetOut = runOrdinaryRecordAt ordSetId
        match ordSetOut.Result with
        | TRError diag -> Assert.Fail("Expected ordinary record FieldSet to succeed, got: " + diag.Message)
        | _ -> Assert.NotEmpty(ordSetOut.InlineOps)
        let ordRecOut = runOrdinaryRecordAt ordRecId
        match ordRecOut.Result with
        | TRError diag -> Assert.Fail("Expected ordinary record RecordExpr to succeed, got: " + diag.Message)
        | _ -> Assert.NotEmpty(ordRecOut.InlineOps)
