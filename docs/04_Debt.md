# Debt register

Every item here is work owed. The counts were measured on 2026-09-27 in this repository at the state copied from Composer `896ef98`, after the port to the contract. An item leaves this register when the code it names is gone.

## Owed by the compiler service

These are repaired in the clef repository. Alex cannot repair them and must not work around them.

| Item | Where | What is owed |
| --- | --- | --- |
| Analysis at publication | `RevisionPublication.fs` calls `WitnessEmission.tryRead`, `BorrowedViews.operation`, `MappedSpans.forLayout`, `MappedBindings.tryFindCall`, `Mmio.operation`, `ExplicitDemand.operand`, `ObligationDischarge.ofGraph` | Each becomes a Baker recipe that writes rows on the graph. Publication then copies rows. |
| Projection readers | `CallableEmission`, `CallableIngress`, `OrdinaryDemand`, `StorageWitness`, `Meets`, `StringByteStorage`, `MemoryPublication`, `SpatialPublication` | The same. The assessment lists 17 findings in its section 6. |
| Node identity | `NodeId.fresh`, a counter global to the process | A derivation from source. See `03_Node_Identity.md`. |
| Free type variables | `TypeIdentities.ofType` publishes an unresolved variable as `Variable` | Binders of the enclosing declaration are published, and a variable with no binder is refused. |
| Process-wide caches | `ConditionalWeakTable` keyed by graph, in 14 or more readers | Removed with the readers they serve. |
| One fact in two tables | The callable projection republishes `CallableCarriers`, `CallableJoins`, `CallableFlows` and `MutableCallableStorage` of the codata unchanged | The contract holds each fact once. Until then the contract rule of agreement refuses a revision whose two copies differ. |
| Witness units | The revision names no unit of witnessing. Alex chooses its starts and their order in `Traversal/NanopassArchitecture.fs`, `runAllNanopasses` | Decided by the owner. `05_Tests.md` holds the measurement of the edge set. |

## Owed by Alex

| Item | Count | What is owed |
| --- | --- | --- |
| Inspection of a type | 2 sites. `Patterns/MmioPatterns.fs` compares the name of the handle type with the access width. `Patterns/ContinuationPatterns.fs` selects the write path from the type inside a published capture slot. | The fact is published as a row, and the Pattern reads the row. |
| Silent failures | 6 sites | Listed in the assessment, section 5.6: no Meet read as no adaptation, an absent demand row read as nothing omitted, a unit function returning a fabricated zero, a unit value materialized, ownership chosen by first match, and an intrinsic occurrence treated as carrying no value. Each becomes an error that names the node and the missing fact. Most need a row that Baker does not yet write. |
| Exceptions in place of returned errors | 73 uses of `failwith` and `invalidOp` | A refusal is a returned value with a node and a reason. |
| Mutable state in the traversal | 128 lines that use `mutable`, a reference cell, `ResizeArray` or assignment | Record expressions and folds. |
| Random identifier | 1, `Guid.NewGuid` in `Correspondence.beginWholeGraphWitness` | The host supplies the identity of a run, or the revision's identity serves. |
| Value names from the counter | `Traversal/Values.fs`, 229 uses of `NodeId.value` | Names derive from the local index of a stable identity. |
| CIRCT operations emitted in Alex | `Elements/HWElements.fs`, `Elements/CombElements.fs`, `Elements/SeqElements.fs`, and the FPGA branches of the record, function, conditional, numeric and match Patterns | A CIRCT hardware operation belongs to the FPGA realization stage (clef-lang-spec, `backend-lowering-architecture.md`, section 2 and section 7 requirement 1). Alex selects an admitted portable form for the selected platform. The CIRCT backend in Composer emits `hw`, `comb` and `seq`. |
| Port names written by text replacement | `Dialects/Core/Serialize.fs`, `hwOpToString`, case `HWModule` | The serializer replaces `%argN` with the port name in the text of the body. It leaves with the row above. |
| MMIO spelled as LLVM operations | `Dialects/Core/Serialize.fs`, `opToString`, cases `MmioLoad` and `MmioStore` | The middle end emits no `llvm.*` operation (the same section 7, requirement 1). The typed operation is handed to the LLVM pathway, which spells it. Owed with Composer's LLVM backend. |
| Literal storage decided at serialization | `Dialects/Core/Serialize.fs`, cases `GlobalString` and `GlobalMemref` | The terminator byte of a string literal and the initial image of writable storage are published facts. The serializer spells them. |
| Raw text operation | `MLIROp.RawMLIR`, emitted by `Traversal/SMTTransfer.fs` for three comment lines | A typed comment operation. No operation of the vocabulary is free text. |
| Match elimination built in the Pattern | `Patterns/ControlFlowPatterns.fs`, `pBuildMultipleMatchElimination` | The Pattern reads the tag, builds a comparison for each arm and nests the conditionals. The selector and the case labels are published, and the Pattern composes one `scf.index_switch`. |
| Structure search for the result of a function body | `Witnesses/LambdaWitness.fs`, one use of `findLastValueNode` | The same search was removed from three witnesses on 2026-09-27 with no change in any test, because the witness of a block binds the block to the value it forwards. The lambda use also feeds the callable, sequence and lazy projections of the result, and is removed with the review of that witness. `findLastValueNode` is deleted with it. |
| Emission after an error inside a region | `Witnesses/ControlFlowWitness.fs`, `Witnesses/MatchWitness.fs`, `Witnesses/LambdaWitness.fs` | A witness inside a region returns an error, the region returns the operations of its other occurrences, and the enclosing witness composes them. The transfer returns `Error`, so no artifact is produced. The enclosing witness is to return the error and emit nothing. |

## Owed by the contract

An error in Alex has three possible owners: the witness, the compiler service, and the contract. They are independent. The rows below are facts that a Pattern needs and that `Fidelity.PSG` does not declare, found on 2026-09-27 at Fidelity.PSG `5476a6e`. Each is repaired in the contract, then written by a Baker recipe, then read by the Pattern. Until then the code named in the last column computes the fact in Alex.

| Fact | State of the contract | Computed in Alex |
| --- | --- | --- |
| Slot of a union tag | `SettledLayout.Union` declares the cases, the payload offset, the size and the alignment. It declares no tag slot. | `Patterns/MemoryPatterns.fs`, `pExtractDUTag` and `pDUCaseAt`, and `Patterns/ControlFlowPatterns.fs`, `pBuildMultipleMatchElimination`, use `i8`. |
| Conversion between numeric families | `NumericOperationKind` has no conversion case. | `Patterns/ApplicationPatterns.fs`, `pTypeConversion` and `pTruncate`, select `fptosi`, `sitofp` and the index casts from the MLIR types. |
| Identity adaptation, and the occurrence a meet is keyed by | `Codata.Meets` has a row where an adaptation exists. A missing row and an identity are the same to a reader. The contract does not state whether the operand of a meet is the declared child or the occurrence that yields its value. | `XParsec/PSGCombinators.fs`, `adaptOperand` and `pPublishedAdapt`, read no row as no adaptation. `adaptOperand` reads the meet at the declared child and then at the occurrence `lastValueNode` finds. That search is removed after the contract declares both, because its removal before that produces an unadapted operand and no error. |
| Omitted formals of a callable | `Emission.Ordinary.Parameters` has a row where a formal is omitted. | `Traversal/CallableOperands.fs` and `Traversal/NanopassArchitecture.fs` read no row as the empty set. |
| Selected platform | `Revision.Platform` declares the Register and Pointer widths. The selected target is a field of `Alex.Generation.Request`. | `Generation.fs` selects the module form, the constraint text and the width check from `request.Target`. |
| Width of `Char` and `Unit` slots | `SettledSlot.Char` and `SettledSlot.Unit` declare no width. | `Dialects/Core/Types.fs`, `SettledScalar.tryType`, uses `i32` for both. |
| Signedness of a borrowed view index | `BorrowedViewOperation` declares the layout and the span. It declares no index transport. | `Patterns/MemoryPatterns.fs`, `indexCastForRange`, selects the cast from the range. |

## Owed by Composer

| Item | Where | What is owed |
| --- | --- | --- |
| Backend reads operation values | `BackEnd/LLVM`, `BackEnd/CIRCT`, `BackEnd/AIE`, `Core/WitnessArtifacts.fs` | Decision D6: MLIR text or bytecode with correspondence records. |
| Platform facts read again from declarations | `CompilationOrchestrator.fs`, `BackEnd/MCU/Target.fs`, `BackEnd/MCU/XtensaTarget.fs` | The revision publishes them. |
| JSON through .NET libraries | Nine files use `System.Text.Json` | `Fidelity.Data`, by the owner's direction. |
| Intermediates written inline | `Core/ProofDispatch.fs`, the backends | Independent sinks, one per layer. `Core/IntermediateSinks.fs` is the first. |

## Retired

| Item | Date | How |
| --- | --- | --- |
| Emission reads wrapped in `Ok`, 69 sites in 32 files | 2026-09-27 | Each site reads the projection directly. The branch for a failed read is deleted. No test outcome changed. |
| A missing publication classified as "not a sequence" | 2026-09-27 | By construction. A revision always carries its emission. |
| A kernel ingress failure dropped | 2026-09-27 | Reported as `CCS8403` at the declaration, in the compiler service. |
| An output with no pin dropped from the hardware plan | 2026-09-27 | Refused, in the compiler service. |
| No tests in this repository | 2026-09-27 | `tests/Alex.Tests` holds the tests of Patterns, witnesses and the traversal, given revisions assembled from contract values. See `05_Tests.md`. |
| A revision was not examined before witnessing | 2026-09-27 | `Alex.Generation.generate` applies `Fidelity.PSG.Integrity.check` and refuses a revision that is not well formed. |
| A declaration queued by a refused occurrence was placed by the next occurrence | 2026-09-27 | The queue of a refused occurrence is emptied. `Traversal/NanopassArchitecture.fs`. |
| An operand with no registered type reported as a disagreement | 2026-09-27 | `Patterns/MemoryPatterns.fs`, `pMemoryBuffer` names the operand and the defect. |
| The serializer wrote two operations and a new value name for one `ReinterpretCast` | 2026-09-27 | `Dialects/Core/Serialize.fs` writes one `memref.reinterpret_cast`. `Elements/MLIRAtomics.fs`, `pTypedExtract` and `pTypedInsert`, return an error for a field of another element type or at an offset. `pTypedExtractView` and `pTypedInsertView` compose that view with a named offset value. |
| `scf.for` had no induction value and was written with its operands in the wrong positions | 2026-09-27 | `SCFOp.For` declares the induction value. One line changed in each of Composer `Core/WitnessArtifacts.fs` and `BackEnd/LLVM/RequirementRealization.fs`. No witness emits the operation yet. |
| Environment reads and console output, 3 and 10 | 2026-09-27 | Removed from `Traversal/NanopassArchitecture.fs`, `Witnesses/ControlFlowWitness.fs` and `Witnesses/LambdaWitness.fs`. Alex reads no environment variable and writes nothing to the console. |
| Structure search for the value of a condition, a branch, a match arm and a module value initializer | 2026-09-27 | `Witnesses/ControlFlowWitness.fs`, `Witnesses/MatchWitness.fs` and `Witnesses/BindingWitness.fs` recall the declared child. Five uses of `findLastValueNode` removed. No test outcome changed in Alex or in Composer. |
| Inspection of the type of a node, 3 sites | 2026-09-27 | `Patterns/EagerPatterns.fs` reads `Emission.Callable.ValueShapes` and `UnitNodes`. `Patterns/EnvironmentPatterns.fs` reads `ValueShapes`. No test outcome changed. |
| The cast of a register write was selected by comparing widths, and its unit result was an `i32` constant of the Pattern | 2026-09-27 | `Patterns/MmioPatterns.fs` reads the published meet through `pSettledAdaptTo` and composes `pWithUnitResult`. Tests: `MmioPatternTests`, two cases, both of which fail on the previous Pattern. No test of a register access existed before. |
| Coverage statistics with no caller | 2026-09-27 | `CoverageStats`, `calculateStats` and `formatStats` deleted from `Traversal/CoverageValidation.fs`. No reference existed in Alex or Composer. |
| A conditional was emitted after a branch region returned an error | 2026-09-27 | `witnessBranchScope` in `Witnesses/ControlFlowWitness.fs` and `Witnesses/MatchWitness.fs` returns the error. The witness returns it and emits nothing. Test: `ControlFlowOccurrenceTests`, which fails on the previous witness. |

## Not debt

The contract mirrors the compiler service's publication types name for name. That was chosen so that the port changed opens and reads, and left every Pattern's logic as it was. The shape of the contract is open to redesign when its binary layout is declared.
