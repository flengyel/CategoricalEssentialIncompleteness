# Categorical domain terminology: scoped source pass

The reviewed uses of *domain* that named a restriction idempotent have been replaced by *restriction idempotent*. Ordinary domains of numerical partial functions and explicitly typed subobjects used as the left legs of partial-map spans remain distinct mathematical objects; they have not been renamed as idempotents.

Scope: all occurrences of `domain` and `domains` in the main section sources and appendices, excluding the introduction and categorical preliminaries owned by the parent. Context around each surviving use was inspected. This is a terminology and local typing pass, not a fresh audit of the body proofs.

## Implemented changes

| Source and anchor | Change and type distinction |
| --- | --- |
| Section 3 opening, “The diagonal argument compares” | Source and target pairs are restriction idempotents. The paragraph now describes inverse images of the target pair rather than saying a morphism “avoids domains”; the target need not have split idempotents. The source conditional equations are described as agreement after composition with the complementary restriction idempotents. |
| Section 8 realization, “Thus evaluation defines” | Removed “exactly these source domains.” The evaluations define total morphisms from the two displayed source objects. The preceding representation-independence statement about numerical partial-function domains remains. |
| Section 6 corollary proof, “In Pfn” | States preservation of binary joins of restriction idempotents directly, rather than naming unions of their partial-function domains. |
| Section 7 lemma title | “Representation of the diagonal restriction idempotents.” The lemma labels and all statements remain unchanged. |
| Section 7 comparison proof, “The theorem therefore” | The interpreted join is distinct from the identity; the text no longer calls its two restriction idempotents theorem/refutation domains. |
| Section 7.4 numerical structure proof, equation `bar f=e` | Explains totality of the displayed represented function on `D_e` and membership of its values in `D_d`, avoiding the ambiguous phrase “source domain.” These sets and the displayed function are already defined. |
| Section 7.5 numerical proof | Joins are **partial identities on unions** of c.e. subsets, not themselves unions of domains. Preservation is stated for the joins. |
| Section 9 subsection heading | “Complementary restriction idempotents and inseparability.” |
| Section 9 complementary-idempotent proof | Names the total inclusions through which the idempotents split, then the component carriers `C_j,C'_j` and their membership searches. The carriers are c.e. subsets; they are not the idempotents. |
| Section 9 compatible-extension paragraph | Identifies the jth component of the refutation restriction idempotent as a partial identity on the displayed inverse-image set. |

## Retained uses and their referents

| Sources | Retained referent |
| --- | --- |
| Section 5.1 and Section 5 internal syntax | Numerical graph predicates, a program's set of defined inputs, the subobject presenting an admissible substitution input, and exact graph conditions for finite-derivation evaluation. `domain inclusion` denotes a subobject and its monic inclusion in the span representation, not the restriction idempotent itself. |
| Section 6 interpretations | Domains of actual partial functions in `Pfn`, including the set inclusion that splits a partial identity. |
| Section 7 arithmetic | Explicit sets `D_0,D_1` of natural numbers and their partial identities under the standard interpretation. |
| Section 7.3 uniform sentence construction | The graph and defined-input equations for the numerical partial function interpreting the proof-search morphism. |
| Sections 7.4–7.5 numerical realization/application | Domains of the represented partial functions, explicitly identified c.e. subsets `C,C'`, and the coded images that form left legs of partial-map spans. |
| Section 8 Miller construction | Numerical partial-function defined-input sets, including representation independence of domains and values. The free-for substitution subobject is a genuine input subobject, not a name for an idempotent. |
| Section 9 cosheaf construction | Component partial-function domains and the explicit subfunctor that represents the left leg of the Turing partial-map span. |
| Appendix B | Explicit domain subfunctors `D_f`, their components `(D_f)_j`, and monic left legs of partial-map spans. The text defines these subobjects and distinguishes their partial identities. Composition uses their actual pullbacks and intersections. |
| Appendix C | Ordinary sets on which the numerical functions and their oracle-restricted representatives are defined. |
| Cross-reference labels throughout | Labels such as `cor:domain-incompleteness` and `eq:syntactic-derivation-domain` are internal identifiers and remain unchanged. |

No legacy expression such as “restriction domain,” “theorem domain,” “refutation domain,” or “diagonal domain” remains in the owned prose. The ordinary and span-subobject uses above retain their stated types. No new historical attribution was added by this agent; that belongs to the parent's source check.

KLR consultation: Section 1, especially points 10–13, was read in the supplied text. The changes apply its attention to connected explanation and identified variables; the user's vocabulary preference is not attributed to KLR as a rule.

## Changed-source identities

| Source | SHA-256 |
| --- | --- |
| `sections/03-sections-and-inseparability.tex` | `26175f2da0198a7710748e57083aa7490f0f1295fb5ebd5dfbc457ae8a5caae2` |
| `sections/04-miller-sequences.tex` | `9e24d7332b4c6cff89ca74b1c8c8cbb0b559bccd305e7142141c2c70aa6b9b83` |
| `sections/06-interpretation-in-models.tex` | `57be993cc95e618b0bf7ba9b9da652173145b4a64015717a349dbbc18e5bf122` |
| `sections/08-essential-incompleteness-of-arithmetic.tex` | `abf8ed7a20fb312bcc5e15ac3734f6943404d5fd99ff40ba654812bf6fe352e3` |
| `sections/08c-numerical-realization.tex` | `861e34e3a588c9e07ae1b6fbb622d6ff4568d22a6db9fcacd988f572445f4188` |
| `sections/08d-numerical-incompleteness.tex` | `1c50baab15f666707d5bda718abc6d2787b2427b098c52a3d42294d37457a6fc` |
| `sections/09-three-point-space.tex` | `7ab696ccfae2653c23abf16e6f4875cbefb44acbf983896bed72b6e2c6203bfb` |
