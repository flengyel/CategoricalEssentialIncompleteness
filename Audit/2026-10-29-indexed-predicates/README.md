# Indexed predicate formulation, 29 October 2026

The subsequent requested plugin reviews are available as
[the hostile author-side audit](HOSTILE_REVIEW.md) and
[the mathematical-writing review](MATHEMATICAL_WRITING_REVIEW.md).
They assess the original five-page note; the resolution record below describes
the resulting revisions. Neither report is a human journal referee report.

The companion note `manuscript/definability_indexed_predicates.tex` rewrites the
ordinary categorical argument. It does not replace or silently change the pinned
v16 manuscript. The existing Lean declarations below already contain the
non-enriched mathematical implication; no Lean source was changed for this note.

## Reviewed source and existing outline

The reviewed material consists of v16's definability definitions and
inseparability proof, its ordinary corollary `thm:integration-diagonal`, the
ordinary Lean files listed below, the numerical adequacy statement, and the
relevant one-object definitions in the earlier v3 manuscript. This is a focused
reconstruction, not a review of the entire v16 manuscript.

The relevant v16 subsections proceed through: enriched restriction structure;
predicate objects and representation pullback; structure-preserving morphisms;
internal inseparability and its ordinary corollary; Boolean presentations; and
Boolean quotients. Their respective roles are definitions, representation,
morphisms, the obstruction theorem, an interpretation of predicates, and the
quotient application.

## Changes of presentation

| Source anchor | Issue for the present task | Repair |
| --- | --- | --- |
| v16, `sec:definability-algebras` | Starts with hom-objects, before identifying the ordinary computational and predicate structure. | Begin with the actual recursion category and its total maps. |
| v16, `thm:integration-diagonal` | The ordinary theorem follows the internal theorem even though it has a direct proof. | Make the indexed-lattice theorem the main argument and prove it directly. |
| v16, `eq:v8-representation-pullback` | A section is stronger data than the ordinary proof needs. | Define the external representation relation and require one witness for each complementary pair. State the chosen-selector version separately. |
| `represented_extension_incomplete` | Its location in a file about Boolean quotients can conceal that its hypotheses mention no Boolean object or quotient. | State its direct predicate formulation immediately after inseparability. |
| Numerical interpretation | Ordinary subsets and full PER subobjects must not be conflated. | Give powersets as an explicitly separate ordinary example; retain the existing PER model in the formalization. |
| v3, chosen indexing and representation operations | Forgetting choices changes the category relevant to the free-extension adjunction. | Distinguish existential data from chosen operations and specify their morphisms. |

The governing writing source was Knuth, Larrabee, and Roberts, *Mathematical
Writing*, Section 1: self-contained theorem statements (point 5), connected
exposition and defined variables (10--11), motivation (12), stable notation
(14--15), and direct opening paragraphs (24). The move to the indexed-lattice
formulation is a mathematical and expository decision, not a rule attributed
to that source.

## Definition order and algebraic status

The note defines total maps and restriction products before the context category.
It introduces the domain functor as `E:C^op→BDLat` before giving its object
and morphism assignments, writes the latter as `E(f^op)`, and states both
functor laws. Bounded lattice homomorphisms precede P and j;
substitution and its row maps precede representation; complementary pairs
before separation; and separation before the theorem. The fibration is built
explicitly from P, with its cartesian lifts specified. The proof's square has
typed arrows and a displayed verification.

The central structure is a recursion category, an indexed bounded distributive
lattice over its total maps, a natural injective domain map, substitution,
distinguished predicates, and existential representation. No terminal object in
the total-map category or quantifier adjoints are required. Therefore the note
uses “indexed bounded distributive lattice” rather than an unqualified
“hyperdoctrine.” Cockett--Lack, *Restriction categories I*, Sections 4.1--4.2,
supplies the antecedent restriction-idempotent functor and fibred-semilattice
terminology; stable joins are additional assumptions here.

## Existing formalization

| Declaration | Mathematical role |
| --- | --- |
| `PredicateLattice`, `PredicateEmbedding` in `Diagonal.lean` | The two indexed lattices and their natural injective comparison. |
| `DiagonalData.Represents`, `DiagonalData.Separates` | The two equations of representation and two separator inequalities. |
| `DiagonalData.diagonal_collapse`, `DiagonalData.inseparable` | The ordinary contradiction and existential representation theorem. |
| `restrictionPredicates`, `restriction_inseparable` in `RestrictionPredicates.lean` | Domain functor derived from actual restrictions and total maps. |
| `represented_extension_incomplete` in `BooleanQuotients.lean` | The direct extension theorem, without a Boolean object or quotient. |
| `Numerical.domainPredicates`, `Numerical.predicates`, `Numerical.domainEmbedding` | Actual numerical domains and their embedding into PER subobjects. |
| `represents_all_pairs_iff` in `ArithmeticAdequacy.lean` | Equivalence with strong numeralwise definability. |

The note uses a shorter version of the existing diagonal calculation: pull both
representation equations to U first, obtain opposite inequalities, then use
injectivity of j. No point, constant map, uniform computable selector, or
application of a Turing morphism is needed in that calculation. The numerical
interpretation supplies genuine recursive substitution and constant representing
arrows; the recursion category alone does not supply representability.

## Preserved distinctions

- V16 explicitly specifies the cartesian monoidal category `(V, ×, 1)`. Its Set
  enrichment is valid. The new note extracts the ordinary argument rather than
  declaring the internal theorem invalid.
- A monoidal category of recursion categories with its Cartesian product does
  not supply the proposed nondegenerate recursion-category-valued enrichment.
  That separate obstruction is not needed in the rewritten proof.
- The base theory need not be c.e. Its theorem/refutation predicates may lie
  outside the domain sublattice. The c.e. extension supplies the two domains used
  in the final corollary.
- The direct arithmetic consequence does not construct a Lindenbaum PER or
  identify all categorical Boolean quotients with theory extensions.

## Verification

The exact LaTeX source was compiled with `latexmk -pdf -interaction=nonstopmode
-halt-on-error`, including the rerun for labels and citations. Mathematical review
covered the full companion note. Two repairs were made during review: the local
arithmetic application now explicitly assumes strong definability of every
recursive set; the unqualified assertion of an essentially algebraic
classification was removed in favor of the displayed operations and equations.

The final log has no warnings, undefined references, or overfull/underfull boxes.
All five rendered pages were inspected, including the typed diagonal square;
there is no clipping or overlap. `git diff --check` passed. No new Lean build is
claimed for this prose-only change.

## Requested plugin review and revision

The HostileRefereeGPT — Cat/Rec and Mathematical Writing plugin instructions
were applied to the complete original note. The mathematical audit found no
confirmed fatal or major defect. Its local numerical-product coding issue is
resolved by an explicit recursive pairing bijection and transported products.
The companion source review verified all three references, including Heller's
full text in the supplied Library copy.

The revised note states `j` as a monomorphism in `[C^op, BDLat]`, with each
component an order embedding. This is equivalent to the former componentwise
injectivity condition: pointwise kernel pairs prove the forward implication;
componentwise cancellation proves the reverse. The new naturality square and
theorem statement use that categorical formulation.

The revision also introduces the lattice category before the domain functor,
states the restriction-product uniqueness equation, types the fibration
factorization, moves chosen representatives after the main proof, removes
repeated qualifications, and states arithmetic essential incompleteness as
Corollary 5.2. The arithmetic paragraph explicitly defines the c.e. theory
convention. The nontriviality and strong-definability hypotheses remain in their
respective theorem statements.

No separate category V or internalization construction is used or introduced.
The statement is about an ordinary recursion category, two indexed bounded
distributive lattices, their natural monomorphism, and representation.

The final revised source compiles without warnings, undefined references, or
overfull/underfull boxes. All five pages were inspected after the final edits;
the naturality square and diagonal proof are legible and unclipped. The entire
final source was read continuously after the prose changes. No Lean code was
changed or rebuilt for this review.
