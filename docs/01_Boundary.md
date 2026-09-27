# The boundary

## The rule

Alex operates on the Program Semantic Graph and on nothing else. The compiler service elaborates and saturates the graph, and Baker settles every decision about the program in it. Alex receives the result.

When Alex needs a fact it cannot read, one of two things is true:

1. The graph is not fully elaborated and saturated. Baker owes the fact, and the fact must be published.
2. Alex is repeating work Baker already did. The code in Alex is deleted.

There is no third case.

## How the rule was broken

Until September 2026 Alex was compiled inside the Composer assembly, and Composer referenced the whole compiler service. Every analysis module of the compiler service was callable from every witness. The separation was a convention.

An inventory taken with the compiler's own symbol resolution, at Composer `896ef98` and clef `b77f888`, measured what the convention had allowed. The script is `tools/CcsSurfaceInventory.fsx`. The rows are in `docs/evidence/ccs-surface-at-notch.tsv`.

| Measure | Count |
| --- | --- |
| Source files in the middle end | 88 |
| Files that referenced the compiler service | 79 |
| Uses of compiler service symbols | 3,937 |
| Distinct record and union types read | 72 |
| Distinct union cases matched | 223 |
| Distinct record fields read | 414 |
| Distinct functions called | 23 |

Most of those uses were reads of data types. The 23 functions are the part that mattered most, because each one ran compiler code on behalf of a witness.

## What replaced each call

| Former call in a witness or pattern | Replacement |
| --- | --- |
| `WitnessEmission.tryCallable`, `tryStorage`, `tryOrdinary`, `tryBoundary`, `tryNumeric`, `tryMemory`, `trySpatial`, `tryRead` | `revision.Emission` and its seven projections |
| `SemanticGraph.tryGetNode` | `Revision.tryNode` |
| `graph.Codata.Value` | `revision.Codata` |
| `BorrowedViews.operation`, `BorrowedViews.layout`, `MappedSpans.forLayout` | `revision.Foreign.BorrowedViews` |
| `Mmio.operation` | `revision.Foreign.Mmio` |
| `MappedBindings.tryFindCall` | `revision.Foreign.MappedCalls` |
| `ExplicitDemand.operand` and the scan of graph edges for demand relations | `revision.Demand` |
| `ObligationDischarge.ofGraph` | `revision.Obligations` |
| `PlatformContext.tryWidth` | `revision.Platform` |
| `applySubst` on a checker type | Removed. A published type is already frozen. |
| `PhaseConfig.isVerbose` | Removed. Alex prints nothing about files because it writes none. |
| A node's metadata map, read for obligation anchors | `node.ObligationAnchors` |

## What enforces the rule

`build/Boundary.targets` runs before every compile of Alex.

| Code | Refused |
| --- | --- |
| ALEX001 | A source line that names the compiler service |
| ALEX002 | A project reference other than the contract and the library the contract references |
| ALEX003 | MLIR rewriting, a process start, or a plugin load |

The compiled assembly confirms it. `Alex.dll` references `Fidelity.PSG`, `FSharp.Core`, `XParsec` and the .NET runtime assemblies.

## Where the debt went

The boundary was enforced first. The analysis that witnesses used to request now runs once, in the compiler service, when the revision is published. That analysis still happens at publication and not in a Baker recipe. It is recorded as debt in `04_Debt.md` and in the header comment of `RevisionPublication.fs` in the clef repository.

Moving a computation from a witness to the publication step does not make the computation correct or complete. It makes the computation's owner the compiler service, which is where a repair can be made.
