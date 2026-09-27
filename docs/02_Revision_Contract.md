# The revision contract

A revision is one published state of the Program Semantic Graph. The compiler service produces it. Alex, the backends, Lattice, Bozzetto and any other tool read it.

The contract is the project `Fidelity.PSG`, in its own repository. The compiler service produces revisions of it. Composer, as orchestrator, obtains a revision from the compiler service and hands it to Alex. No reader needs the compiler's repository to read a revision.

## Decisions the owner has agreed

| | Decision |
| --- | --- |
| D1 | The contract is a PSG revision schema in its own project, `Fidelity.PSG`. The compiler service produces revisions of it. Its binary layout is declared with BAREWire facilities. The contract does not reside in BAREWire. |
| D2 | Types are frozen. Quantified type and measure variables have explicit binders. A free variable with no binder is a refusal. No checker cell, deferred computation, callback or platform context crosses. |
| D3 | Alex is its own project. Its input and output are language-neutral, and it holds no process-global state. |
| D4 | The boundary is enforced first. Projections computed at publication are carried as debt until Baker recipes produce them. |
| D5 | Node identity is derived from source and is stable across revisions. |
| D6 | Alex hands the backend MLIR text or bytecode with declared correspondence records, and not values of Alex's own operation types. |

## What is built

| Decision | State |
| --- | --- |
| D1 | Built as immutable F# types with a producer in the compiler service. The binary schema is not written. |
| D2 | Types cross as `TypeIdentity`, with every substitution applied. The refusal of a free variable is not enforced, because the binders of an enclosing declaration are not yet published. |
| D3 | Built. Alex reads three environment variables for tracing and creates one random identifier per run. Both are listed as debt. |
| D4 | Built. |
| D5 | Not built. The identity is the compiler's counter value. See `03_Node_Identity.md`. |
| D6 | Not built. Composer still reads Alex's operation values. |

## Proposals the owner has not ruled on

These four were proposed as D7 to D10. Each is stated here as a question with its consequence.

### D7. How are the bytes of a revision laid out?

There are two ways to encode a graph as bytes.

A stream encoding writes each value after the previous one. A reader finds the hundredth node by reading the ninety-nine before it. BARE's message encoding is a stream encoding.

An offset-indexed layout writes fixed-width records and a table of positions. A reader finds the hundredth node by reading one table entry and going to that position.

The proposal is the offset-indexed layout, built on BAREWire's memory tier. A witness visits nodes in traversal order and looks up facts by node identity, so it needs the second kind of access. The file on disk holds the same bytes as the buffer in memory.

### D8. Where does JSON come from?

Today the compiler writes JSON files of the graph while it compiles, and the cost is paid on every compile.

The proposal is that the compiler emits the binary revision only. JSON is rendered from the binary by a separate reader when a person or a tool asks for it. The reader is shipped with the format, so inspection of an intermediate stays available.

The owner has directed that JSON work uses `Fidelity.Data`, and that intermediates are written by independent sinks that do not delay the pipeline. The JSON reader of a revision is the first such sink.

### D9. Who may read the buffer?

A managed array belongs to one process. A second process cannot read it without a copy.

The proposal is that a revision's buffer is memory-mapped and position-independent from the first version. Position-independent means every reference inside the buffer is an offset from the start of the buffer, never a machine address. Any process can then map the same bytes and read them where they are. A sink in a separate process depends on this. A pinned managed array remains available as a convenience inside one process.

### D10. How many readers are written?

Alex, the JSON reader, Bozzetto, Lattice and agents all read revisions. If each wrote its own reader, each would hold its own opinion of the layout.

The proposal is one reader library, generated from the schema. It is read-only. It reads through a byte source that each host supplies: a span in .NET, a `DataView` in Fable, a memref in Clef. It depends on no host library.

## Requirements found while building

- The revision header carries the contract version and the producer. The producer is a name today. An implementation epoch is owed.
- A revision that Alex receives is complete. It is never a pruned dump.
- The rewrite record of the nanopasses is not in the revision. It is owed, either inside the revision or referenced from it.
- A number in a JSON value of `Fidelity.Data` is a 64-bit float. An exact integer above 2^53 needs a string form or an integer case. Obligation constants and addresses reach that range.

## How the producer fills the contract

The compiler service holds its own types, which carry checker state. The contract holds published types, which carry none. The file `RevisionMappers.fs` in the clef repository copies one to the other, field by field. It is generated by `tools/PSGContract/GenerateMappers.fsx`, which stops with a named difference when a contract type and its counterpart disagree on a case or a field.

The file `RevisionPublication.fs` assembles the revision. It is the only place a graph leaves the compiler service.
