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
| D1 | Immutable F# contract types and the compiler-service producer are built. The contract now also has a generated indexed binary layout and reader over BAREWire, with a separate .NET mapping owner. See D7–D10 for requirements and remaining implementation gaps; this is not complete consumer or port acceptance. |
| D2 | Types cross as `TypeIdentity`, with every substitution applied. The refusal of a free variable is not enforced, because the binders of an enclosing declaration are not yet published. |
| D3 | Built. Alex reads three environment variables for tracing and creates one random identifier per run. Both are listed as debt. |
| D4 | Built. |
| D5 | Not built. The identity is the compiler's counter value. See `03_Node_Identity.md`. |
| D6 | Not built. Composer still reads Alex's operation values. |

## Required indexed revision architecture: D7–D10

The owner has directed implementation of these four decisions. They govern the
work now; the implementation gaps below remain work to complete, not decisions
awaiting permission. Representation, lifetime and semantic acceptance are
separate contracts.

### D7. Offset-indexed revision images

A revision has a position-independent, offset-indexed layout built on BAREWire's
memory tier. Fixed-width directory entries identify each child's offset and
extent; scalar leaves use bounded BARE encodings. Disk, mapped memory and a
received buffer hold the same image bytes. Reading preserves every published
identity and settled fact.

`Fidelity.PSG.Binary` now supplies the generated layout and reader. Opening a
view validates the envelope and sorted node index and materializes that index.
`tryNode` then reads a selected node without decoding preceding node bodies.
Opening or reading one node is not complete structural admission:
`readRevision` reads every published field and runs the integrity check. Other
fact tables currently use that complete reading. Source proof discharge and
current-source authority remain outside representation validation.

### D8. JSON inspection through Fidelity.Data

The required interchange output is the binary revision. A separate reader
shipped with the format must render its graph as JSON on demand using
`Fidelity.Data`. Inspection belongs to independently owned sinks, not inline
semantic work in the compiler or a serializer in Alex. A sink's lifetime and
completion remain owned by its host.

The separate [Fidelity.PSG.Json reader](../../Fidelity.PSG/src/Fidelity.PSG.Json/README.md)
now implements this boundary. It consumes the shared `Binary.readRevision`
operation before generated writers render every published field with Fidelity.Data.
There is no runtime reflection, separate binary decoder or semantic repair.
Wide integers and exact decimal/floating representations retain their meaning.
The explicit `PsgInspect` process owns its mapping and output sink; compiler
publication neither renders JSON nor starts or waits for that process.
Bozzetto's MCP base64 envelope remains a transport projection, distinct from
this graph reader. Compiled reader checks do not establish acceptance of actual
socket-delivered images, deployment, other host ports or performance.

### D9. Shared image bytes and explicit mapping ownership

Image references are offsets from the image's start, never process addresses.
Hosts must support reading the same completed immutable image from mapped
memory, including a separate process with the appropriate resource access.
Publication and reader lifetimes must keep those bytes stable.

`Fidelity.PSG.Hosting.MappedRevision` now supplies a separate .NET file/mapping
owner. Its reads serialize with disposal; retained views refuse access to the
disposed source. The portable contract owns no file or mapping handle.
`ByteSource.ofArray` provides an owned-copy convenience for a received or local
buffer; it does not pin an array or establish a zero-copy path. The current
mapping adapter copies bounded ranges. Cross-process deployment and performance
acceptance must be demonstrated separately.

### D10. One generated reader over host byte sources

Alex, inspection sinks, Bozzetto, Lattice and agents share the format's reader
instead of implementing independent interpretations of the layout. The reader
performs representation access only. Each host supplies a bounded, stable byte
source and owns its availability and disposal: .NET memory, a Fable `DataView`,
or a Clef memref. These host resources and callbacks never become semantic
fields of a revision.

The generated PSG reader now uses BAREWire's `ByteSource`; array and .NET mapped
adapters use the same decoding rules. Alex currently receives a fully read
immutable `Revision`, not a byte-source view. Fable and Clef host adapters and
their acceptance remain unimplemented here. The shared boundary is required;
the .NET implementation does not prove those ports or their performance.

The [indexed image architecture](../../Fidelity.PSG/docs/Indexed_Revision_Architecture.md)
and [format description](../../Fidelity.PSG/docs/Binary_Images.md) describe the
current reader and lifetime boundaries. They do not replace source, witness,
backend or transport acceptance evidence.

## Requirements found while building

- The revision header carries the contract version and the producer. The producer is a name today. An implementation epoch is owed.
- A scope that Alex receives is complete for its authorized occurrences and
  settled boundaries. Completeness does not require retained unused library
  bodies. Baker owns live scope selection and dependency closure; publication
  copies its stored rows. Alex cannot turn a retained graph into a scope by
  filtering it. Initial service attachment supplies demanded scopes; subsequent
  delivery changes affected scopes against the exact resident base. The current
  complete-`Revision` reader and manifest do not yet implement that delivery
  contract.
- The rewrite record of the nanopasses is not in the revision. It is owed, either inside the revision or referenced from it.
- A number in a JSON value of `Fidelity.Data` is a 64-bit float. An exact integer above 2^53 needs a string form or an integer case. Obligation constants and addresses reach that range.

## How the producer fills the contract

The compiler service holds its own types, which carry checker state. The contract holds published types, which carry none. The file `RevisionMappers.fs` in the clef repository copies one to the other, field by field. It is generated by `tools/PSGContract/GenerateMappers.fsx`, which stops with a named difference when a contract type and its counterpart disagree on a case or a field.

The file `RevisionPublication.fs` assembles the revision. It is the only place a graph leaves the compiler service.
