# Node identity

Status: proposal. Decision D5 is agreed. The scheme is the owner's to choose, and nothing in this document is built.

## What exists

A node's identity is an integer taken from a counter that is global to the compiler process (`NodeId.fresh` in the compiler service). The contract publishes that integer as `NodeId`.

The integer depends on the order in which the compiler created every node before this one. An edit to one declaration changes the identity of every node created after it. Two compilations of the same source agree only when they run the same steps in the same order in a fresh process.

Alex uses the identity in three ways:

| Use | Count |
| --- | --- |
| As a key into published tables | every table of the revision |
| In the text of an error | most of 229 uses of `NodeId.value` |
| To derive the names of emitted values | `Traversal/Values.fs` |

The third use places the integer in the MLIR text. An unchanged function is emitted with different value names after an unrelated edit, so its text cannot be compared with the text from the previous revision.

### Observed on 2026-09-27

One fixture, built by the same code from the same source, was run twice in the Composer test suite. Its failure names a node.

| Run | Node named in the failure |
| --- | --- |
| Four test classes selected by filter | 429 |
| The whole suite | 185 |

Nothing about the fixture differed. The tests that ran before it in the same process differed, and each of them had taken identities from the counter.

## What D5 requires

1. An unchanged declaration has the same node identities in the next revision.
2. Identity is a function of the source. It does not depend on a counter, on the order of compilation, or on the process.
3. Nodes that elaboration and saturation add have identities under the same rule.
4. Identity is compact and ordered, so that it serves as a table key in a binary layout.
5. The MLIR text of an unchanged declaration is byte-identical in the next revision.

## Proposed scheme

### Regions

A region is one top-level declaration together with everything elaborated from it. Lambdas nested in the declaration belong to its region.

A region has two values:

| Value | Derived from | Changes when |
| --- | --- | --- |
| Region identity | The declaration's qualified path. For a specialization, the path and the frozen identities of its type arguments. | The declaration is renamed or moved. |
| Content hash | Every settled row of the region: node kinds, payloads, frozen types, and the published facts keyed by its nodes. | Anything in the region changes. |

The identity names the region. The content hash states whether the region changed. Baker decides which regions are in the change frontier. Alex compares identity and content hash, and reads nothing else to decide what to witness again.

### Nodes

A node's identity is the pair of its region and its local index.

The local index is the node's position in a fixed order of the region's settled tree. The order places the declaration's own node first, then the nodes of its signature in declaration order, then the body in preorder.

Signature nodes come first so that an edit to a body leaves the local indices of the signature unchanged. A reference from another region targets the declaration or a node of its signature. Such a reference therefore survives an edit to the body it refers into.

The order is a function of the settled tree. It does not depend on the order in which recipes ran.

### Facts that span regions

A joint fact has sources in more than one region. It belongs to a joint region. The identity of a joint region is derived from the role of the fact and the identities of its participating regions, in sorted order. A change to any participant changes the joint region's content hash.

### Layout

| Form | Content | Size |
| --- | --- | --- |
| Inside one revision | Index into the revision's region table, and the local index | Two 32-bit integers |
| Across revisions | Region identity, and the local index | The region identity is a truncated cryptographic hash |

A reader compares nodes inside one revision by the compact form. A comparison across revisions goes through the region table.

### Value names

A value name is derived from the local index and the ordinal of the value at that node. MLIR value names are scoped to a function, and a function lies inside one region, so the region does not appear in the name. Symbol names are derived from the declaration's path, as they are today.

## Alternatives considered

| Alternative | Why it is not proposed |
| --- | --- |
| Reset the counter for each compilation | Removes the dependence on the process. An edit still shifts every later identity. |
| Derive identity from the source range | An edit above a declaration moves its range. |
| Derive identity from content alone | Two identical subtrees receive one identity. A change to a leaf renames every ancestor. |

## Questions for the owner

1. Is the top-level declaration the right unit of a region, or should each lambda be its own region?
2. Is the region identity derived from the path, as proposed, so that an edit to a body keeps it?
3. Which hash function and width are used for region identity and content hash? BAREWire would own the choice.
4. Is the instantiation key of a specialization the list of frozen type identities of its arguments?
5. Is the rule for the local order accepted: declaration, signature in declaration order, body in preorder?

## What this requires of the compiler service

The identity is assigned where the graph is saturated. Baker assigns region membership when a recipe adds a node, and the final order is computed once, after saturation and before publication. The process-global counter is then removed. That work is in the clef repository and is owed.
