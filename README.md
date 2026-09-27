# Alex

Alex is the witness stage of the Composer compiler for the Clef language. It reads one published revision of the Program Semantic Graph (PSG) and emits MLIR.

Alex was part of the Composer repository until September 2026, as the directory `src/MiddleEnd`. It is now its own project, so that the separation between the compiler service and the witness stage is a fact of the build.

## What Alex depends on

| Dependency | Purpose |
| --- | --- |
| `Fidelity.PSG` | The published form of the PSG. It is its own project. The compiler service produces revisions of it, and Composer hands one to Alex. This is the only description of a program Alex receives. |
| `BAREWire` | The library the contract references for declared platform types. It reaches Alex through the contract. |
| `XParsec` | Parser combinators. Patterns are composed with them. |
| `FSharp.Core` | The host language's core library, for as long as .NET hosts the compiler. |

Alex does not reference the Clef Compiler Service. The build refuses a source line that names it.

## Entry

```fsharp
Alex.Generation.generate : Request -> Result<Witnessed, Refusal>
```

A `Request` holds the revision, the selected target, and the libraries the project declares. The entry examines the revision with the structural rules of the contract (`Fidelity.PSG.Integrity.check`) and refuses one that is not well formed before any witness runs. A `Witnessed` value holds the operations, their portable text, the correspondence records, the writable storage inventory, the transcription of the proof obligations, and the link requirements. A `Refusal` holds the reason and the operations witnessed before the refusal.

## Layout

| Path | Content |
| --- | --- |
| `src/Alex/Dialects` | MLIR types and operations, and their serialization to text |
| `src/Alex/Elements` | One MLIR operation each |
| `src/Alex/Patterns` | Compositions of Elements over published facts |
| `src/Alex/Witnesses` | One category of node each |
| `src/Alex/Traversal` | The Huet zipper, the single traversal, value names, coverage checks |
| `src/Alex/XParsec` | Combinators over the revision |
| `src/Alex/Correspondence.fs` | Scope, occurrence and emitted-definition records |
| `src/Alex/Generation.fs` | The public entry |
| `build/Boundary.targets` | The boundary, checked before every compile |
| `tests/Alex.Tests` | Tests of Patterns, witnesses and the traversal, given revisions assembled from contract values |
| `docs` | The boundary, the contract, the open decisions, the debt register and the account of the tests |
| `tools` | `CcsSurfaceInventory.fsx` measured the dependency on the compiler service. `PlanMeasure.fsx` measures what the edge set of a revision says about units of work. |

## Build

```bash
dotnet build src/Alex/Alex.fsproj
```

The contract is expected at `../Fidelity.PSG/src/Fidelity.PSG/Fidelity.PSG.fsproj`. A different location is set in `Directory.Build.local.props` through the property `PsgContractProject`.

```bash
dotnet test tests/Alex.Tests/Alex.Tests.fsproj
```

`docs/05_Tests.md` states what a test is given and how one file is run alone.

## State

Alex builds against the contract alone. Composer references this project, asks the compiler service to publish a revision, and hands the revision to Alex.

The revision is an immutable value in memory. Its binary form is not yet built. The documents in `docs` state what is decided, what is proposed and what is owed.

## History

The files under `src/Alex` were copied from Composer at commit `896ef98`. Their earlier history is in the Composer repository under `src/MiddleEnd`.
