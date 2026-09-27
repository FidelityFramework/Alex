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

## Owed by Alex

| Item | Count | What is owed |
| --- | --- | --- |
| Inspection of a node's type | 5 sites: `EagerPatterns`, `EnvironmentPatterns`, `ContinuationPatterns`, `MmioPatterns` | A witness branches on the shape of a type. The fact it needs is published, and the witness reads the fact. |
| Silent failures | 6 sites | Listed in the assessment, section 5.6: no Meet read as no adaptation, an absent demand row read as nothing omitted, a unit function returning a fabricated zero, a unit value materialized, ownership chosen by first match, and an intrinsic occurrence treated as carrying no value. Each becomes an error that names the node and the missing fact. Most need a row that Baker does not yet write. |
| Exceptions in place of returned errors | 73 uses of `failwith` and `invalidOp` | A refusal is a returned value with a node and a reason. |
| Mutable state in the traversal | 128 lines that use `mutable`, a reference cell, `ResizeArray` or assignment | Record expressions and folds. |
| Environment reads | 3, for `COMPOSER_TRACE_TRAVERSAL` and `COMPOSER_TRACE_CONTROLFLOW` | Tracing is requested in the `Request`, and trace output is returned as a value for a sink. |
| Console output | 10 uses of `printfn` | The same. |
| Random identifier | 1, `Guid.NewGuid` in `Correspondence.beginWholeGraphWitness` | The host supplies the identity of a run, or the revision's identity serves. |
| Value names from the counter | `Traversal/Values.fs`, 229 uses of `NodeId.value` | Names derive from the local index of a stable identity. |
| Target forms in common Patterns | Record, function and conditional Patterns branch on the target | Target forms belong to the backend. |
| Serialization beyond spelling | `Dialects/Core/Serialize.fs` | The assessment lists the cases in its section 5.8. |
| Tests | None in this repository | Tests that build a revision directly from contract values. The existing tests are in Composer, because they build their source through the compiler service. |

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

## Not debt

The contract mirrors the compiler service's publication types name for name. That was chosen so that the port changed opens and reads, and left every Pattern's logic as it was. The shape of the contract is open to redesign when its binary layout is declared.
