# Outline and private-source dependency inventory

Prepared before the self-contained revision, on 29 October 2026.
The baseline mathematical source remains dated
30 October 2026; this inventory does not change that date.

Baseline: `manuscript/local_connectedness_and_essential_incompleteness.tex`,
*Local connectedness, range functors, and essential incompleteness*.
SHA-256:
`1078044059fe239c27fdc82a9b69e7995e3b28c03d7310ff1ffb4164948d439f`.
The entire source was read again before preparing this inventory.
No mathematical source was edited by this reviewer.

The current request has two parts. Correct the literature sentence so
that failure to require preservation of the near product is not presented
as a feature introduced by the errata. Remove citations to the private
LOC manuscript and the companion three-point manuscript, supplying the
actual mathematical arguments required by the paper. Removing citation
commands alone does not meet the second requirement.

The mathematical-writing plugin and its complete workflow were applied.
The supplied Knuth–Larrabee–Roberts excerpt was reread: Section 1,
points 1–19, printed pp. 1–3, PDF pp. 3–5, from Library file
`libfile_53ef001c39508191895fe913d122fc16`. The outline implements the
verified advice on self-contained statements (5), connected explanations
(10–11), motivation and reading order (12), and readable prose when
formulas are skimmed (13). The inventory format and body–appendix
allocation are editorial recommendations, not rules attributed to Knuth.

## Actual baseline outline

| Section | Mathematical function |
| --- | --- |
| Abstract | Announces arithmetic essential incompleteness, explains recursive inseparability, previews faithful model interpretation and effective three-point theories. |
| 1.1 Recursion categories and incompleteness | Gives Di Paola–Heller and Rosolini context, defines recursive separation and essential incompleteness, compares Bernardi. |
| 1.2 Local connectedness and comparison functors | Introduces connected domains and lifting; compares Heller and Lengyel 2004; cites LOC for the theorem, join criterion, and counterexample. |
| 1.3 Syntactic categories and the present applications | Distinguishes uniform and pointwise provability, explains the model-family construction and effective step, previews the cited three-point construction. |
| 2.1 Partial maps and domains | Defines restrictions, total arrows, zeros, domains, separation, inverse images, ranges, and splitting. |
| 2.2 Products, coproducts, and local connectedness | Defines the structural operations, range functors, connected domains, partial monomorphisms, sections, and weak choice. |
| 2.3 Recursion categories | Defines prodominical, isotypical, the Turing morphism, and the adopted recursion-category convention. |
| 3 The syntactic recursion category | Constructs `S_T` using one uniform provable graph-equivalence sentence and verifies its operations. |
| 4 Interpretation in models | Constructs each `F_M` and proves preservation. |
| 5 A faithful family and theory extension | Constructs `D_T` and `F_T`, proves target properties and faithfulness, and defines the extension square. |
| 6.1 The local-connectedness construction | Proves the connected alternative, the section proposition, and range-functor lifting. All three proofs are already present. |
| 6.2 Lifting in the syntactic category | Constructs the selection program and applies the theorem to `S_T`; explains target/source separation. |
| 7 Effective observations and essential incompleteness | Applies the theorem to `Rec → Pfn`, connects finite computations to PA proofs, and derives the arithmetic conclusion. |
| 8, opening | Defines the topology, cosheaves, computational fork diagrams, and partial maps; states the universal diagram, frames, and recursion-category conclusion by reliance on the companion. |
| 8.1 Local connectedness and lifting | Gives a short connected-domain argument, imports structural properties and equality failure, and applies the full inclusion. |
| 8.2 Endpoint functors | Defines component and probe functors; proves endpoint universality using a Turing morphism whose full construction is imported. |
| 8.3 Proof observations and extensions | Defines syntax and rules, imports consistency and finite proof construction, proves the numerical observation theorem and incompleteness of computational extensions. |

The main line is already suitable: categorical inseparability, syntactic
interpretation, effective arithmetic observation, and a genuine
nonnumerical instance. The missing self-contained material is concentrated
in the three-point construction; the main LOC proof is not missing.

## Every explicit LOC dependency

Line anchors below refer to the baseline hash and are not locations in
the eventual expanded paper.

| Baseline anchor | Imported content | Already present? | Required disposition |
| --- | --- | --- | --- |
| §1.2, lines 110–123, “The inseparability theorem of…” | The range-functor lifting theorem and explanation of its hypotheses. | The full theorem and proof are present in §6.1. | Present it as the paper's theorem and refer internally to `thm:local-lifting`; avoid an unsupported novelty claim. |
| §1.2, lines 124–125, Proposition 4.8 | Joins of parallel arrows with disjoint domains supply the required lift. | No proof is present. | Add a short proposition with proof in §6.1 after the theorem, or omit the ancillary claim if it is not retained. The preferred allocation is the body because the argument is short and explains a usable criterion. |
| §1.2, lines 125–126, Section 4.5 | All the other target/functor hypotheses can hold while lifting fails and the source diagonal pair is separable. | No construction or proof is present. | Add the oracle-domain counterexample with its closure, Turing, range, and failed-lift verifications in an appendix; use an internal reference in the Introduction. |
| §6 opening, lines 539–542, Theorem 4.7 | Identifies the local-connectedness theorem whose remaining condition is lifting. | Full statement and proof follow in the same section. | Replace the external citation with the internal theorem reference. |
| §6.1 opening, lines 545–548, Section 4.3 | Construction of the section from connected domains, splitting, and weak choice. | Lemma `lem:connected-alternative` and Proposition `prop:local-switch` include their proofs. | Remove the private-source attribution and keep the mathematical motivation and proofs. |
| Proof of `thm:local-lifting`, lines 646–647, Theorem 4.7 | Attribution of the inseparability theorem. | The proof is explicit, including the typed Turing factorization and the use of totality only after applying `F`. | Start the proof with its actual argument rather than a private citation. Preserve its source/target totality distinction. |
| Bibliography, lines 1127–1129 | LOC bibliographic entry. | Not a proof dependency itself. | Remove after all citations have been replaced by internal statements. |

The short join criterion needs only the restriction-order upper-bound
equations. For `d=(i_1 c)∨(i_0 c′)`, they give its two branch equations;
the two complementary domains lie below its restriction, proving
totality. The target uniqueness result then identifies its image with the
required section. It need not assert that the functor preserves arrow joins.

The counterexample must define the category before asserting its
properties: domains are c.e. relative to the halting set, value maps admit
ordinary partial recursive extensions, and total arrows are ordinary total
recursive maps. It must verify composition and structural closure, ranges,
and the Turing-morphism parameterization using ordinary recursive index
substitution. The exhibited categorical separator is nonrecursive, so the
imported sentence saying the pair can be “recursively separable” must not
be copied: the proved conclusion is **separable in this category**. The
failed selecting map is total and nonrecursive. The optional no-common-
upper-bound argument then explains failure of the join criterion.

## Every explicit companion dependency and its hidden prerequisites

| Baseline anchor | Imported content | Already present? | Needed material and proposed allocation |
| --- | --- | --- | --- |
| §1.3, lines 182–185 | The computational cosheaf construction and existence of its nonnumerical recursion category and logical presentation. | Only a preview; body currently imports essential claims. | Rewrite as a preview of the paper's own §8 and appendices after those constructions have been included. |
| §8 opening, lines 839–843, companion §2 | Equivalence between cosheaves on the three-point space and fork diagrams. | Object values and pushout are stated, but inverse functor and equivalence proof are omitted. | Add the short proof in the body: classify covers, construct the pushout on the largest open, define maps by its universal property, and identify the two natural isomorphisms. |
| §8 opening, lines 845–861 | Existence of the partial-map category, componentwise monomorphisms, and ranges. These rely on the structure subsequently cited in §8.1. | Definitions and assertions, without their finite-limit or image verification. | Appendix A should prove finite limits, componentwise monicity, c.e. image factorization and pullback stability, then the span/domain description and range agreement. |
| §8 opening, lines 863–880, companion §§4–5 | Universal diagram `V`, restriction embeddings of every diagram into it, product/coproduct/word frames, isotypical recursion subcategory, and identification of its splitting. | The diagram and properties are stated; the embedding, frames, and full Turing morphism are not constructed. | Appendix A should supply explicit coordinate maps and inverses, the compatible Turing morphism, its total parameter morphism, and the restriction-splitting argument. Keep `V`, the theorem statement, and an internal reference in the body. |
| §8.1, lines 887–890, companion Proposition 2.2 | Splitness, weak choice, ranges, coproducts, and inverse-image laws. | The connected-domain detection argument is present; the other properties are imported. | Prove the structural facts in Appendix A. Include zeros, products and `f×0=0`, since the recursion-category conclusion uses them. Distinguish the inverse-image laws needed by the theorem from any stronger general range-category claim. |
| §8.1, lines 901–902, companion Proposition 6.1 | Failure of decidable equality on `V`. | The five-subobject nonnumericality argument is already given; equality failure is only cited. | Add the short naturality/diagonal contradiction in the body or Appendix A. If retained, define the intended decidable-equality test rather than merely naming the property. |
| Proposition `prop:endpoint`, lines 922–923 | The displayed compatible Turing morphism from the companion. | Endpoint formula and endpoint universality are proved; the central map and its exact domain are absent. | Point to the actual Turing construction in Appendix A. Its central computation must halt exactly when the central program halts and the two endpoint computations agree with its projections. Prove that every partial diagram factors via a total parameter map. |
| §8.3 opening of logical construction, lines 1012–1013, companion Theorem 6.3 | Existence and consistency of the classical presentation, finite formula/proof carriers, and selected theorem range. | The signature, initiality's meaning, Hilbert schemes, modus ponens, and extension definitions are present. The finite constructions and consistency proof are not. | Appendix B should construct these objects and maps and prove consistency. Refer to that internal theorem before defining the observed extension pairs. |
| §8.3, lines 1039–1045 | One-node proof maps and `t_0 ν* t_0=0` are attributed to the imported consistency theorem. | The inequalities and consistency equation are displayed, but no one-node maps or consistency argument is supplied. | Define the positive and negative proof injections on the split domains and derive the range inequalities. Prove consistency in Appendix B without a global separator or Boolean equality on `V`. |
| Bibliography, lines 1130–1134 | Companion bibliographic entry. | Not itself mathematical evidence. | Remove after all dependent claims have proofs or internal references. |

The companion's proof of its Theorem 6.3 itself cites a further private
iteration/proof note for finite-stage unions, typed folds, and
equality-constraint consistency. Copying that theorem and its current
proof would simply move the private dependency one level back. The new
paper must either include those arguments at the generality actually
claimed or give a direct finite-tree construction for this concrete
computational diagram category. The latter is sufficient for the present
statement and keeps the appendix focused.

The direct construction must still supply mathematical proofs, not a
reference to an unspecified “ordinary coding.” Required points include:

- the c.e. formula and derivation carriers at each component;
- recursive total transitions acting on formulas and derivations, with
  the appropriate preservation of rule instances;
- the total constructor and conclusion maps;
- initiality of the formula algebra in the **total** diagram category,
  by the unique recursive fold and its naturality;
- the theorem image as a selected c.e. subdiagram, its rule closure,
  and leastness if the paper states that stronger property;
- the signed one-node proof injections and their range inequalities;
- a finite proof of consistency that needs neither a global Boolean
  separator of the disjoint axiom domains nor decidable internal atom
  equality.

If an appendix claims parameter-stable finite-stage initiality or Heller's
full word/iteration structure, those stronger claims require their own
proofs. They need not be added merely because the companion contains
them. The current paper needs the explicit finite-word frames and finite
syntax/proof objects used by its construction; it does not use a general
range completion theorem. The companion's range-completion discussion is
therefore outside this import.

## Recommended body–appendix allocation

Retain the present eight main sections and their main results. The
following additions supply the missing proof chain without interrupting
the arithmetic construction.

1. **Introduction.** Correct the near-product sentence and replace all
   private-source references by internal theorem/appendix references.
   State that the three-point construction is developed in this paper.
2. **Categorical preliminaries.** Retain the current definitions. Add
   only definitions that newly included arguments actually need, such as
   the adopted internal equality test if its failure is retained.
3. **The syntactic recursion category.** Retain the construction.
4. **Interpretation in models.** Retain the construction.
5. **A faithful family and theory extension.** Retain the construction.
6. **Switching and the local-connectedness theorem.** Keep the existing
   proofs. Add the short disjoint-arrow-join criterion after the general
   theorem. Give a brief mathematical pointer to the counterexample
   appendix, if that result is retained.
7. **Effective observations and essential incompleteness.** Retain the
   actual numerical application and arithmetic proof.
8. **Computational cosheaves and effective observation.** Add the short
   cosheaf/fork equivalence proof; state the computational-structure and
   compatible-Turing results with internal proof references. Retain the
   local connectedness, endpoint/probe arguments, syntax/rule definitions,
   and observed-extension theorem. Use the appendix's consistency theorem
   rather than an imported assertion.
9. **Appendix A: The computational fork category.** Prove finite limits,
   images, structural partial-map laws, weak choice, universal embedding,
   the three frames, the compatible Turing morphism and total
   parameterization, and the recursion/splitting conclusion. Include the
   short equality obstruction if it is not in the body. Order these so
   that neither the Turing morphism nor its component laws are used before
   construction.
10. **Appendix B: Finite syntax, proofs, and consistency.** Give the
    actual finite carriers, natural transitions, total algebra folds,
    rule-instance/proof constructions, theorem image and atomic
    inequalities, and the finite-support/equality-constraint consistency
    argument needed for this category.
11. **Appendix C: A range functor without the lifting property.** Give
    the oracle-domain counterexample and all properties used in its
    comparison with the main theorem. This is separate from the main
    applications and can be read after their positive constructions.

Appendix lettering may follow the actual integration order. The essential
requirement is that every body invocation have a precise internal result,
and that each appendix prove its own prerequisite claims rather than
redirect the reader to a private note.

## Local wording correction

The current sentence “These are iteration functors; preservation of
products is not required in the corrected theorem” should be deleted.
The qualification belongs in the preceding sentence citing the original
article and the corrections. Proposed wording, preserving the current
description of the functors, is:

> Lengyel extended this existence argument using faithful functors that
> preserve domains, coproducts, zero maps, and iteration, but need not
> preserve the near product \cite{Lengyel2004,Corrections}.

The qualification applies to the original result as well as its
corrections. It must not be described as a new weakening supplied by the
errata. The exact mathematical list of preserved structures remains a
primary-source verification matter; the user's correction fixes the
near-product point.

## Checks after integration

The next writing review should read the complete integrated source,
including every appendix, and update the actual outline before judging
it. It should inspect the abstract, Introduction, theorem statements,
cross-references, and bibliography for remaining dependence on the two
private sources. Search both citation keys and titles/filenames; absence
of a citation key alone does not prove that the arguments are present.

The proof review must check the mathematical imports rather than treat
this inventory as their certification. In particular, preserve exact
partial domains in the compatible Turing proof, distinguish total
parameter morphisms from arbitrary partial parameters, and verify the
finite consistency proof at the stated internal level. No source
revision, compilation, or proof verification has been performed for
this outline.

## Final integrated layout and scope

The inventory above records the pre-revision source and proposed allocation.
The integrated source is dated 29 October 2026 and has SHA-256
`99b760671b51bafe038fa371ca9814d9de55dd53b8099487a3d6d8d44f73bc21`.
The final request requires every mathematical dependency used by the
paper, including its Introduction, to be supplied internally. The actual
theorem **retains** its lifting hypothesis. Appendix C is explicitly a
counterexample to the statement obtained **by dropping** that hypothesis;
it is not a counterexample to the theorem as stated. This resolves the
intermediate uncertainty about whether to include the example.

The disjoint-arrow-join criterion is included as
`prop:disjoint-joins`. It is the criterion already stated and proved as
Proposition 4.8 in the private LOC manuscript. The baseline *present paper*
relied on that citation without reproducing the proof; the inventory did
not identify a missing result in the LOC source.

The implemented outline is:

1. **Introduction**, with the existing three subsections. The original
   Lengyel-2004 near-product qualification is incorporated in the sentence
   citing the article and corrections. The Introduction describes the
   paper's own inseparability theorem and three-point construction and
   points internally to the criterion and the example with lifting dropped.
2. **Categorical preliminaries**, with partial maps/domains;
   products/coproducts/local connectedness; and recursion categories.
3. **The syntactic recursion category.**
4. **Interpretation in models.**
5. **A faithful family and theory extension.**
6. **Switching and the local-connectedness theorem**, now with three
   subsections: the local-connectedness construction; a sufficient
   condition for lifting; and lifting in the syntactic category.
7. **Effective observations and essential incompleteness.**
8. **Computational cosheaves and effective observation**, with the
   original local-connectedness/lifting, endpoint-functor, and
   proof-observation subsections. Every formerly imported construction
   has a precise reference to an internal result.
9. **Appendix A: The computational fork category.** Its five subsections
   treat cosheaves/numerical diagrams; partial maps/ranges/connected
   domains; universal diagram/frames; the Turing morphism; and the
   recursion category/splitting. The cosheaf equivalence proof is here
   rather than in the body. Finite limits, image laws, weak choice,
   universal embeddings, explicit frames, the full compatible Turing
   morphism, its exact-domain total parameterization, nonnumericality,
   and equality failure are all included.
10. **Appendix B: Finite syntax and proofs in the computational diagram
    category.** Its two subsections construct the syntax algebra and
    prove total-category initiality, then construct the c.e. proof
    object and theorem range, prove leastness and atomic inclusions,
    and prove consistency with a finite valuation.
11. **Appendix C: Dropping the lifting hypothesis.** The oracle-domain
    category, structural closure, Turing morphism, range functor,
    categorical separator, failed selecting-map lift, and absent common
    upper bound are constructed and verified in the text.

The private bibliographic entries and citation keys have been removed.
There is no replacement dependence on another private finite-iteration
note and no free range completion in the argument. Appendix B proves the
concrete finite construction needed here rather than asserting a more
general iteration result. The complete-source writing review and local
repairs are recorded in `WRITING_REVIEW.md`; mathematical hostile review
and final rendering verification follow separately.
