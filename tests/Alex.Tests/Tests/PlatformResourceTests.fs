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
              DeclarationPath = [ acqBinding ]
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
              DeclarationPath = [ relBinding ]
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
