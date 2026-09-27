# Rules for work in this repository

These are owner requirements. They apply to every change, by a person or an agent.

## The boundary

- Alex receives one published revision of the Program Semantic Graph and nothing else. The revision is a value of `Fidelity.PSG.Revision`.
- Alex references the published contract, `Fidelity.PSG`, and the library the contract references. The contract is its own project. Alex references no compiler and no file of the compiler's repository. `build/Boundary.targets` refuses any other project reference (ALEX002) and any source line that names the compiler service (ALEX001).
- A fact Alex lacks is missing from the revision. The repair is made where the graph is elaborated and saturated, in Baker, and the fact is then published. A witness never computes the fact, infers it, or asks another component for it.
- Reading a fact through a function of the compiler service counts as a compiler call, including a function that only reads.

## What a witness does

- An Element spells one operation. A Pattern composes Elements over published facts. A Witness observes one node at its occurrence in the Huet zipper and returns what its Pattern produced.
- A witness performs no analysis, no selection of width or representation, no recovery of structure, and no repair after emission.
- A witness that cannot proceed returns an error that names the node and the missing fact. It never returns a default, a zero, a skip or an empty result in place of an error.
- A value name is a derivation from the node it belongs to. No witness holds a counter, a pool or a budget of names.

## What Alex produces

- Alex returns operations, their portable text, and the correspondence between each emitted definition and the occurrence it was witnessed at.
- Alex opens no file, writes no file and starts no process. Text produced beside the module is returned as a value. The host, or a sink the host owns, decides what is kept.
- Alex holds no serializer for JSON, TOML or any other interchange format.
- MLIR-to-MLIR rewriting, declaration hoisting and plugin loading are prohibited (ALEX003).

## Working rules

- Use .NET tooling, shell tools and `dotnet fsi`. Do not introduce or run Python.
- Prefer record expressions and folds. Do not add mutable accumulators.
- Do not add a package reference where a Fidelity Framework library covers the need.
- The terms Elaboration and Saturation name phases of the graph's construction in Baker. Do not use them for anything in Alex.
- Record exact evidence and exact failures. A focused check that passes does not establish that the compiler accepts a program.

## Tests

- A test in this repository states a revision from values of the contract. It references no compiler, and the boundary gate applies to test files.
- A fixture states the rows the compiler service publishes for it. Where the compiler service refuses the fixture, the fixture states the rows the Pattern under test reads and says so in its comment.
- A test of a refusal requires the refusal text, no emitted operation and no bound operand. An assertion that cannot fail is removed.
- A test whose input comes from Clef source text, or which enters a Composer backend, resides in the Composer repository.
- A test that fails because of a defect in Alex stays as written. The defect is repaired in `src/Alex`, or recorded in `docs/04_Debt.md` with the evidence.
