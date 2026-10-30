# Writing review of the self-contained integration

The integrated source supplies internal proofs for the mathematical
dependencies inventoried in `OUTLINE.md`. The range-functor theorem retains
its lifting hypothesis. The disjoint-arrow-join criterion is stated and
proved, and Appendix C treats precisely the statement obtained by dropping
that hypothesis. The three-point construction now has explicit structural,
Turing-morphism, syntax, proof, and consistency arguments. The three local
writing repairs reported during this review have been made. No further
consequential exposition defect is identified in the reviewed source.

Reviewed paper: *Local connectedness, range functors, and essential
incompleteness*, dated 29 October 2026.
Source: `manuscript/local_connectedness_and_essential_incompleteness.tex`.
SHA-256:
`99b760671b51bafe038fa371ca9814d9de55dd53b8099487a3d6d8d44f73bc21`.
The complete main text, Appendices A–B, and bibliography were read in
order; the subsequently integrated Appendix C, revised Introduction, and
local repairs were then read. The mathematical source was not edited by
this reviewer. This report concerns exposition and dependency presentation,
not certification of the new proofs or their originality.

The mathematical-writing plugin was applied. Its full workflow and the
supplied Knuth–Larrabee–Roberts excerpt were reread: *Mathematical Writing*,
Section 1, points 1–19, printed pp. 1–3 (PDF pp. 3–5), Library file
`libfile_53ef001c39508191895fe913d122fc16`. Verified principles used here
are self-contained statements (5), connected prose and complementary
explanation (10–11), reader motivation (12), readability when formulas are
skimmed (13), consistent notation (14), and unambiguous sentences (17).
The author's stricter first-use requirement continues to govern the
abstract. The tables and dependency inventory are editorial methods,
not a format prescribed by that source.

## Actual outline

| Location | Function |
| --- | --- |
| Abstract | States the arithmetic result, explains classical inseparability, and describes model interpretation, provable selection, and the effective three-point application. |
| §1.1 | Introduces the Di Paola–Heller problem, Rosolini's framework, recursive separation, essential incompleteness, and Bernardi's antecedent. |
| §1.2 | Explains local connectedness and lifting, distinguishes existence and inseparability results, states the corrected near-product qualification, previews the join criterion and the conclusion when lifting is dropped. |
| §1.3 | Distinguishes unprimed and primed syntactic systems, explains the faithful model-family construction, separates it from effective arithmetic observation, and previews the three-point application. |
| §§2.1–2.3 | Defines restrictions, domains, ranges, splitting, products/coproducts, range functors, connectedness, weak choice, and the adopted recursion-category/Turing-morphism conventions. |
| §§3–5 | Constructs the uniform syntactic quotient, model functors, faithful family, target properties, and theory-extension square. |
| §6.1 | Proves the connected-domain alternative, the section construction, and the general range-functor lifting theorem. |
| §6.2 | States and proves the sufficient disjoint-arrow-join criterion. |
| §6.3 | Constructs the syntactic selecting program and applies the theorem to `S_T`. |
| §7 | Applies the local-connectedness theorem to classical numerical recursion, connects finite computations to proofs, and derives arithmetic essential incompleteness. |
| §8, opening | Defines cosheaves, the topology, computational diagrams, partial maps, the universal diagram, and frames; identifies the internal construction results used. |
| §§8.1–8.3 | Explains nonnumericality and lifting, constructs endpoint/probe functors, and proves incompleteness of the stated computational extensions using the internally proved logical presentation. |
| A.1, Cosheaves and numerical diagrams | Proves the cosheaf equivalence, distinguishes categorical from global pointwise operations, and proves finite limits, images, regularity, and extensivity. |
| A.2, Partial maps, ranges, and connected domains | Proves the span/domain description, restriction structure, splitting, weak choice, range agreement/pullback laws, finite domain operations, and local connectedness. |
| A.3, A universal diagram and computable frames | Constructs restriction embeddings, word formation, and explicit product/coproduct/word isomorphisms. |
| A.4, A Turing morphism | States numerical specialization, defines the endpoint and central computations, checks their domain compatibility, and constructs total parameter maps with exact-domain factorization. |
| A.5, The recursion category and its splitting | Proves the full isotypical subcategory is a recursion category, its inclusion is a range functor, its splitting is the ambient category, and it is nonnumerical; proves equality failure and applies lifting. |
| B.1, The syntax algebra | Constructs the finite formula carriers and transitions and proves initiality in the total diagram category. |
| B.2, The proof object and its range | Constructs c.e. derivations, natural conclusion maps, the least rule-closed theorem domain, atomic inclusions, and consistency by a valuation depending on two finite proofs. |
| C, Dropping the lifting hypothesis | Constructs the oracle-domain category, proves its categorical/Turing properties, and exhibits a categorical separator and a selecting map without a lift. |

The main line remains visible while the computational constructions have
their proofs in appendices. No further structural change is recommended.
The outline's pre-integration recommendation is superseded by its new
final-layout section, which records the actual three appendices.

## Findings and resolved repairs

| Anchor | Difficulty or checked distinction | Principle or rationale | Disposition |
| --- | --- | --- | --- |
| §1.2, Lengyel 2004 sentence | The earlier text made failure to require product preservation sound like a weakening introduced by the corrections. | Accurate attribution and direct comparison of hypotheses. | The sentence citing the original article and corrections now includes “without requiring preservation of the near product.” The separate awkward iteration-functor sentence is gone. |
| §6.2 | The baseline paper cited the sufficient criterion without proving it. | A cited private proof must become an actual internal proof. | Proposition `prop:disjoint-joins` contains the criterion and its proof. This is the result already present as Proposition 4.8 in the private LOC source; it was not missing from that source. |
| §1.2, Theorem `thm:local-lifting`, Appendix C | A counterexample could be misread as contradicting the actual theorem. | Preserve the exact hypothesis being removed. | The theorem keeps lifting; the Introduction and Appendix C explicitly concern the statement with lifting dropped. |
| A.1, the diagram `H` | Literal `H×H=H` depended on an unstated strict product choice. | Distinguish equality and isomorphism; consistent notation. | Replaced by `H×H≅H`. |
| A.3, word construction | “Internal semigroup” left the category of the universal property implicit after discussing a functor on partial maps. | State the category and arrow class of a universal property. | The property now specifies an internal semigroup in `E` and a total diagram map. |
| B.2, proof grammar | “These are all the proof constructors” only repeated the just-completed grammar. | Economy; remove recaps with no further mathematical content. | Deleted. |

The short body explanation of connected central diagrams and endpoint
singletons is retained although Appendix A gives the complete argument.
This is useful complementary explanation: it tells the reader why the
example satisfies the main theorem before the appendix supplies the
component verification. The repetition of the syntax signature and Hilbert
schemes in Appendix B similarly identifies exactly which body construction
is being proved. Neither introduces an alternative presentation.

## Dependency closure and definition order

| Former dependency | Internal location | Reading-order assessment |
| --- | --- | --- |
| Connected-domain alternative and section construction | Lemma `lem:connected-alternative`, Proposition `prop:local-switch` | Their structures are defined in §2; proofs precede the lifting theorem. |
| General inseparability theorem | Theorem `thm:local-lifting` | Full target hypotheses and the partial source lift are stated; the proof uses target totality exactly where needed. |
| Disjoint-arrow-join criterion | Proposition `prop:disjoint-joins` | Restriction order is already defined. The proof does not require preservation of arrow joins by the functor. |
| Failure without lifting | Appendix C, Proposition `prop:missing-lift` | `K`, oracle-domain enumeration, value extensions, and the arrow class precede the proposition. The separation is explicitly categorical, not claimed to be recursive. |
| Cosheaf/fork equivalence | Proposition `prop:fork-cosheaves` | Cosheaves and the topology are defined in §8; the inverse functor and cover proof are given in A.1. |
| Finite limits, monomorphisms, regular images | Proposition `prop:fork-total` | Numerical carriers and diagram morphisms precede the constructions; componentwise descent is proved. |
| Partial-map structure and range laws | Proposition `prop:fork-structure` | Depends internally on the proved total-category structure and gives actual domain/value formulas. |
| Local connectedness | Proposition `prop:fork-local` | Uses connectedness from §2 and the finite component probes constructed in Appendix A. |
| Universal object and frames | Lemmas `lem:fork-dominance`, `lem:fork-frames` | The embedding equations and coordinate codings are explicit; word formation is defined before its frame. |
| Compatible Turing morphism | Theorem `thm:fork-turing` | Specialization and partial-value equality are explained first. Endpoint and central program domains are separate until the compatibility check forms a subdiagram. |
| Recursion category and splitting | Proposition `prop:fork-recursion` | Uses the frames and Turing theorem and specifies both directions of the hom-set correspondence. |
| Nonnumericality and equality failure | Proposition `prop:fork-distinction` | The terminal-subobject invariant is calculated; the intended equality-test map is stated in the proof. |
| Finite syntax and initiality | Proposition `prop:fork-syntax-initial` | The constructor grammar, transition maps, and total polynomial action precede the universal property. |
| Finite proof object, theorem image, atomic inclusions and consistency | Theorem `thm:fork-proof-presentation` | The component carriers, signed leaves, modus-ponens matching, proof transitions and conclusion map are defined before the theorem. |

The earlier private proof chain is not merely replaced by different
citations. Appendix B gives a direct finite-tree construction for this
specific computational category. It does not invoke a private general
iteration theorem, a free range completion, or a presheaf-image assertion.
The finite valuation uses the positive leaves of the two specified proofs
at one component. The concluding explanation distinguishes that use from
an internal Boolean equality map or a global separator; this is a
mathematically relevant qualification, not a review disclaimer.

The established first-use repairs in the abstract and preliminaries remain
in place. The abstract explains recursive inseparability and selection
between disjoint exhaustive cases, and omits `S_T`, split-category,
range-functor, endpoint, and atom-map terminology. The body defines the
Turing morphism through a total parameter map. The appendices do not
replace that term by “compiler” or “evaluator.” Object actions, morphism
actions and variance are explicit for the word, model, component and
syntax functors. Logical negation and inverse image along its constructor
remain distinct.

The appendix-defined material is cited internally before its longer proof;
these are transparent forward references to stated results, not unexplained
local notation. The main argument does not depend on the reader seeing an
external source for those proofs.

## Scope and verification

The complete-source prose pass found mathematical functions for the
paragraphs: definitions, motivation, constructions, proofs, comparisons,
or necessary boundaries of the conclusions. No review-process narration
or LLM-facing instructions were found in the manuscript. A targeted search
also found no private citation keys, the two private titles/filenames,
the former corrected-theorem wording, or the unwanted Turing terminology.
The bibliography no longer contains the LOC or companion entries.

The reviewer inspected rendered pages 2, 9, 14, 18, 21, 22, and 23 of the
24-page integration build preceding Appendix C and the three final local
repairs. Those pages cover the near-product sentence, the complete join
criterion, the main theorem/appendix transition, the Turing statement,
and the syntax/proof/consistency construction. A truncated raster export
of page 22 was regenerated and then inspected. The final Appendix C and
repairs were checked in source. This report does not claim to have run
the compilation or inspected the later complete rendered version; final
build and page checks belong in the separate verification report.

The existing proof review is reused only for unchanged arguments. The
new appendix proofs and imported criterion remain subject to the
subsequent hostile mathematical review. This writing review verifies that
the required arguments are actually present and clearly scoped; it does
not certify every inference in them. Public literature claims are not
independently reverified here beyond their presentation and the author's
near-product correction. No Lean formalization is claimed.

All reported local writing repairs are resolved at the recorded source
hash. The next stage is the hostile review of the integrated mathematical
arguments, followed by the final build and delivery checks.
