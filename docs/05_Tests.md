# Tests

Date: 2026-09-27. This document states where each kind of test resides, what a test of Alex is given, and what was measured while the tests were moved.

## Where a test resides

| Kind of test | Repository | Input |
| --- | --- | --- |
| A Pattern, a witness or the traversal, given facts | Alex, `tests/Alex.Tests` | A revision assembled from values of the contract |
| A source construct carried through publication to the witness, or a Composer backend | Composer, `tests/Alex.Tests` | Clef source text, checked and published by the compiler service |
| A structural rule of the contract | Fidelity.PSG, `tests/Fidelity.PSG.Tests` | A revision assembled from values of the contract |

The tests in this repository reference Alex and the contract. They do not reference the compiler service, and the build gate refuses a test file that names it.

## What a test in this repository is given

A test states a revision. Any value of the contract is an input that Alex either witnesses or refuses with a reason.

| Rule | Statement |
| --- | --- |
| Facts come from the producer | Where the compiler service publishes the fixture, the rows of the test are the rows it publishes. They were printed from the compiler service and copied. |
| Facts the producer refuses | Where the compiler service refuses the fixture, the test states the rows the Pattern under test reads, with the values the fixture declares. The comment of the fixture says so. |
| A missing fact | A test of a refusal states the revision without the row, runs the same Pattern, and requires the refusal text, no emitted operation and no bound operand. |
| The entry | Alex examines a revision once, at `Alex.Generation.generate`, with `Fidelity.PSG.Integrity.check`. A test of a revision that is not well formed calls the entry. |

## How to run

```bash
dotnet test tests/Alex.Tests/Alex.Tests.fsproj
dotnet test tests/Alex.Tests/Alex.Tests.fsproj -p:OnlyTests=IndexSwitchTests
dotnet test tests/Alex.Tests/Alex.Tests.fsproj -p:OnlyTests=IndexPatternTests -p:WithFixtures=ArrayRead
```

The second form builds one test file alone. The third adds a shared fixture from `tests/Alex.Tests/Fixtures`. Both properties accept a wildcard. Four component tests run `mlir-opt`, which must be on the path.

## The oracle of a moved test

Each test that moved from Composer has its text at Composer commit `896ef98` as its oracle:

```bash
git -C ../Composer show 896ef98:tests/Alex.Tests/<File>.fs
```

Only the construction of the input changed. The differences from that text are listed below, each with its reason.

## Differences from the oracle

| Test | Difference | Reason |
| --- | --- | --- |
| `IndexPatternTests`, missing memory carrier type | Renamed from "is diagnosed by the composed load element" to "is diagnosed before a load is composed". The text required is `Memory operand:`, the operand and `has no registered type`. | The Pattern examines the operand before it composes a load. `MemoryPatterns.pMemoryBuffer` now names an operand with no registered type. It reported it as a disagreement before. |
| `SequenceBoundaryTests`, suspension boundaries, `SeqExpr` | The owned fixture states the origin of the constructor. The fixture without ownership requires the refusal for the origin. | `SeqWitness` seeks the origin before the frame since Composer commit `a3159ef`. The compiler service refuses this fixture, so the origin row is stated by the test and is not a row it publishes. |
| `MutableClosureTests`, mutable read retracts after a write changes | The refusal text is the one Alex issues for the missing storage row. | Alex reads the revision directly. It cannot issue the text of a publication that could not be read. |
| `LambdaOccurrenceTests`, definition discovered inside a dependency | The traversal starts at each of the three declarations in their order. | A reference does not place its binding since Composer commit `a3159ef`. Each definition is witnessed from its own declaration. Every assertion is unchanged. |
| `RequirementTests`, selected singleton, constant arm | The case requires the refusal of a raw constant arm. | Baker settles a constant arm as a typed equality and a conditional. Alex refuses a raw constant arm since Composer commit `b655e38`. |
| `TraversalOccurrenceTests`, match scrutinee | The match selects by the case of a union, and its scrutinee is a formal. | The oracle used a constant arm, which Alex refuses since Composer commit `b655e38`. Every occurrence assertion is unchanged. |
| `TraversalOccurrenceTests`, invalidated source projection | The test calls the entry and requires the refusal of a revision that is not well formed. | Alex examines a revision at its entry. The traversal driver does not examine it again. |
| `WitnessArtifactTests`, queued globals | The witness of the test returns a value of the published carrier. | The occurrence is a numeric result site, and the traversal refuses a result site that returns no value. |
| `ContinuationPatternTests`, owned child sites | The child sites are the body of the parent generator. | A formal is an argument of the function that declares it. |
| `EnvironmentPatternTests`, two tests | The fixture states the representation of the captured cell. | The Patterns read it. |
| `CallableOperandTests`, two tests | The refusal text is the one Alex issues for the missing carrier row. | Alex reads the revision directly. It cannot issue the text of a publication that could not be read. |
| `CallableOperandTests`, direct physical parameters | The measure variables are read from the frozen type identity. | The compiler service function that read them is not available to Alex. |
| `CallableSymbolTests`, anonymous closure identities | One execution in place of two. | A contract node has no metadata, so both inputs of the oracle are one contract value. |

## What the tests of a retraction examine

At the oracle, a retraction test changed the graph, the compiler service refused to publish it, and Alex then refused a graph with no publication. In this repository the test hands Alex a revision from which the row is withdrawn.

The reviews of the move established a limit of this form. A revision holds some facts in more than one form: a frame in the codata and a protocol in the emission projection, a carrier in the codata and a carrier in the emission projection. Alex reads one form. A revision in which the form Alex does not read was changed, and the form it reads was left in place, is witnessed. The compiler service refuses to publish such a graph, so a published revision does not have this defect. The contract refuses it only where it declares that two tables agree, which it does for four tables of the callable projection.

| Test | The change that only the compiler service refuses |
| --- | --- |
| `SequenceTransportTests`, five cases | A changed frame, formal or signature of a sequence, with the published protocol left in place |
| `MutableClosureTests`, one case | A changed write, with the published storage row left in place |
| `CallableOperandTests`, `CallableFlowTests`, `CallableTransportTests`, the retraction cases | A carrier or a flow changed in the codata, with the emission row left in place. The rule of agreement now refuses this at the entry. |

## Defects found by the move

| Defect | Where | State |
| --- | --- | --- |
| A declaration queued by an occurrence whose result was refused was placed by the next occurrence. | `Traversal/NanopassArchitecture.fs` | Repaired for a refusal by the traversal and for a refusal by the witness. The tests are in `WitnessArtifactTests`. |
| An operand with no registered type was reported as a disagreement. | `Patterns/MemoryPatterns.fs` | Repaired. |
| A conditional records an error for a branch that is not a declared child, and then emits the conditional. | `Witnesses/ControlFlowWitness.fs`, `Witnesses/MatchWitness.fs` | Owed. The transfer is refused because the error is recorded. The operations are emitted into the evidence of the refusal. |
| A missing alias row raises an exception in place of a refusal. | `Traversal/Values.fs` | Owed. It is in the debt register under exceptions. The entry refuses a revision with a missing alias row before any witness runs. |
| A revision held a carrier in two tables, and Alex read them without requiring agreement. | Contract | The contract rule of agreement refuses such a revision at the entry. |

## Rules of the contract that were measured first

Each rule in `Fidelity.PSG.Integrity` was measured on published revisions before it was stated.

| Revision | Nodes | Identities named | Identities not held | Rows missing under the coverage and requirement rules |
| --- | --- | --- | --- | --- |
| `01_HelloWorldDirect` | 5,797 | 269,661 | 0 | 0 |
| A program with two lazy values | 179 | 10,231 | 0 | 0 |
| A program with one numeric operation | 121 | 6,204 | 0 | 0 |
| A program with a record | 106 | 5,052 | 0 | 0 |

The Composer suite publishes a revision for every source-backed test. With the rules applied at the entry of Alex and at the backend entry, no test was refused for the form of its revision.

## What the edge set says about units of work

`tools/PlanMeasure.fsx` reads a published revision and reports the starts the traversal uses today, the region under each start, and the edges that cross between regions. It changes nothing in Alex.

| Revision | Reachable nodes | Starts | Crossing edge ends | Groups when every crossing edge connects | Groups when a reference to a start does not connect |
| --- | --- | --- | --- | --- | --- |
| `01_HelloWorldDirect` | 54 | 5 | 336 | 1 | 1 |
| A program with two lazy values | 93 | 3 | 138 | 1 | 1 |
| A program with three functions and an entry | 40 | 5 | 29 | 1 | 4 |

The relations that cross are demand relations, boundary proofs, numeric proofs and program initialization. A rule that reads connection alone joins every start into one group. A division of the work needs the roles of the relations, and those are settled by Baker.
