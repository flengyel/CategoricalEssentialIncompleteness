# Initial writing audit: reading order and literature context

Baseline reviewed: `manuscript/syntactic_model_range_functors.tex`, titled
*Local connectedness, range functors, and essential incompleteness*, dated
30 October 2026. SHA-256:
`780dec35305daf617191f5dff0f216d89ca0e7b81dccd7e9888180c29a2455e4`.
The complete source was read before this report. The intended renamed
manuscript is `local_connectedness_and_essential_incompleteness.tex`;
no mathematical source was edited by this reviewer.

The author's objection is supported by the source. The abstract presents
many specialized names before explaining them, and the Introduction does
not contain the historical comparison supplied by the Introduction of
`LOCOct10f.tex`. The previous writing report overstated its conclusion by
calling the exposition resolved without a first-occurrence inventory of
these terms. This audit identifies those omissions rather than repeating
that conclusion.

## Governing source and criteria

The mathematical-writing skill and its terminology/source-review references
were applied. The supplied Knuth–Larrabee–Roberts excerpt was reread:
*Mathematical Writing*, Section 1, points 1–19, printed pages 1–3
(PDF pages 3–5), Library file `libfile_53ef001c39508191895fe913d122fc16`.
Relevant verified guidance concerns self-contained statements (5), connected
prose (10), explaining variables at introduction (11), the reader's
motivation and expectations (12), prose intelligible while skimming formulas
(13), consistent notation (14), and unambiguous sentences (17).

The author's present requirement is stricter than the skill's general
permission to preview technical concepts in an abstract. Here an unexplained
specialized abstract term is to be removed or economically explained; its
definition several sections later is not an adequate repair. Standard
mathematical background is distinguished below from manuscript-specific
or specialized terminology. No claim is made that the abstract should
reproduce all restriction-category axioms.

## Actual outline before revision

| Location | Actual function |
| --- | --- |
| Abstract | Announces essential incompleteness, the model-family functor and its lifting property, and endpoint observation of the three-point presentation. |
| §1, paragraph 1 | Names the Di Paola–Heller program and introduces domains, complementarity, and the inseparability obstruction. |
| §1, paragraph 2 | Summarizes the local-connectedness theorem through a list of target hypotheses and the lifting requirement. |
| §1, paragraph 3 | Introduces `S_T`, cites its failure of local connectedness, and previews model interpretation. |
| §1, paragraph 4 | Explains the arithmetic proof/refutation argument and its connection with the local-connectedness theorem. |
| §1, paragraph 5 | Previews the three-point application through endpoints, an atom map, and computational extensions. |
| §1, paragraph 6 | Gives the roadmap. |
| §2 | Mixes restriction notation, the concrete syntactic construction, range calculations, and the Turing-morphism property. |
| §3 | Constructs interpretation in one model. |
| §4 | Constructs the faithful family, inserts definitions of connectedness, splitting, partial monicity and weak choice, proves target properties, and treats theory extension. |
| §5.1 | Finally defines a range functor, constructs sections using local connectedness, and states and proves the lifting theorem. |
| §5.2 | Constructs the syntactic lift and applies the theorem. |
| §6 | Defines classical numerical observations, applies the lifting theorem to `Rec→Pfn`, and proves arithmetic essential incompleteness. |
| §7, opening | Defines the topology, computational fork diagrams, partial maps, and universal object. |
| §7.1 | Establishes local connectedness and lifting for the full inclusion. |
| §7.2 | Defines endpoint evaluation and probes and proves endpoint universality. |
| §7.3 | Defines the selected pair, syntax, rules, atom map, and computational extensions; proves the observation theorem. |

The obstacle is not a missing roadmap. Core structural definitions are
distributed among the applications, while the abstract and Introduction
use the vocabulary of the completed constructions.

## First-occurrence and definition inventory

Locations refer to the baseline above. “Absent” means that a search of the
complete source did not find an explicit definition; it does not mean that
the term is unknown in the literature.

| Term | First occurrence | First explanation | Formal definition or stated construction | Finding and recommended action |
| --- | --- | --- | --- | --- |
| Essential incompleteness | Abstract, sentence 1 | The same sentence gives the PA conclusion: every consistent c.e. extension is incomplete. | §6, arithmetic corollary; the extension notion for §7 is defined separately. | Adequate for the arithmetic claim. Keep this explicit outcome. |
| Recursion category | Abstract, sentence 1 | §1 says it captures partial computations, but gives no criterion. | §2 supplies a Turing morphism and then calls `S_T` prodominical and isotypical; a general definition is absent. | Introduce the adopted definition in preliminary material and cite its source. Avoid making the abstract depend on knowing every variant of the term. |
| Local connectedness | Abstract, sentence 1; again in sentence 2 | §1, paragraph 2: connected domains detect equality of partial arrows. | §4, after the model-family functor is constructed. | Too late for the present abstract requirement. Give a short self-contained description if retained there; move the formal definition earlier. |
| Range functor | Abstract, sentence 2, split over a line break | §1, paragraph 2 lists preserved structures. | Opening of §5, after the model functor has already been discussed. | Remove its name from the abstract or explain its relevant preservation property there. Put the formal definition with the range definition. |
| `S_T` | Abstract, sentence 2 | §1, paragraph 3 explains uniform provable program equality. | §2, equation `eq:uniform` and the preceding object description. | The symbol is unnecessary in the abstract. Replace it there by the description of the category, or define it in the sentence introducing it. |
| Split restriction category | Abstract, sentence 2 | No abstract explanation. §1 invokes splitting as a hypothesis. | §4 says restriction idempotents split; the notation of a splitting appears later in the section proof. | Remove from the abstract. Define splitting with typed maps and equations in preliminaries. |
| Complementary source domains | Abstract, sentence 3 | §1, paragraph 1 gives an informal description. | §2 states `cc'=0` and `c∨c'=1`. | Explain the relevant disjointness-and-coverage condition directly in the abstract, rather than stacking “complementary,” “source,” and “domain.” |
| Target map and lifting | Abstract, sentence 3 | The behavior is partly described there; §1, paragraph 2 says it must be the image of a source arrow. | §5.1, section proposition and `F ell_c=s_c` in the theorem. | The abstract can state that one provably total program realizes the choice in every model. Reserve the source/target lifting terminology for the explanation of the theorem. |
| Recursively inseparable pair | Abstract, sentence 5 | §1 explains categorical inseparability using complemented domains. | §2 defines the domain version; §6 identifies classical domains and separators. | In the abstract explain the classical notion directly: disjoint c.e. sets with no recursive separator. Do not require a reader to reconstruct the set-theoretic meaning from the later categorical definition. |
| Computational cosheaf | Abstract, sentence 6 | §1, paragraph 5 names the example without describing its objects. | §7 gives the three-point topology, fork diagrams, numerical carriers, and partial-map category. | Remove the specialized label from the abstract or describe the fork diagrams directly. In the Introduction give that concrete description before using endpoint language. |
| Endpoint evaluation | Abstract, sentence 6 | §1 refers to the endpoints of a defining fork that has not yet been displayed or described. | §7.2 defines `E_j` on objects and spans. | Remove from the abstract; describe projection to an outer component after the diagram shape is given. |
| Turing morphism | Abstract, sentence 7 | §1 invokes Turing universality without stating it. | End of §2 gives the total-parameter factorization. | This preservation detail can be omitted from the abstract. Retain the established term in the body and introduce the factorization before using it. |
| Atom map | Abstract, sentence 7 | §1, paragraph 5 still names it without explaining its action. | §7.3 defines `theta:V→S` after the syntax algebra. | Remove from the abstract. At its first introductory use say that it regards each parameter as an atomic formula. |
| Computational extension | Last abstract sentence | §1 invokes it repeatedly without defining the class. | §7.3: a rule-closed domain containing `t_0`, with domain equations for consistency and completeness. | The abstract must state the permitted effective class in ordinary mathematical language, or reserve this claim for the Introduction after explaining the class. Avoid suggesting arbitrary extensions. |
| Weak choice; partial monomorphism | §1, paragraph 2 | The phrase lists the hypothesis but does not explain the operation it supplies. | §4 defines both, together with the section equations. | Introduce these together in preliminaries. The Introduction can describe their role as supplying the required partial inverse. |
| Isotypical | End of §2 | “The chosen coding isomorphisms make `S_T` isotypical.” | No explicit definition. | Add the short definition that any two objects are isomorphic before making this assertion. |
| Prodominical | End of §2 | Product with a zero arrow is said to be zero. | No general definition; later it is a theorem hypothesis. | State the adopted definition with its typed zero-product condition and cite the source. |
| Frames | §7, after the displayed universal fork | Names product, coproduct and nonempty-word frames. | No definition; the construction is attributed to the earlier paper. | Define the specific maps meant, or replace the word by the exact typed structure imported from the cited result. Verify whether the relevant maps are isomorphisms or retractions before choosing wording. |

The abstract's principal defect is the cumulative load of the delayed terms,
not merely one missing parenthetical definition. Adding a separate gloss
for every term would make it longer and less readable. Omission of technical
implementation details is the better repair.

## Comparison with the Introduction of LOCOct10f

The supplied `loc_source_review.tex`, Introduction, was read in full and
its cited bibliography inspected. It gives a historical and mathematical
progression that the current Introduction largely omits:

1. Di Paola–Heller's algebraic treatment of partial computation and
   categorical incompleteness.
2. Rosolini's broader `P`-category framework and representation results.
3. Heller's existence theorem and its use of local connectedness, followed
   by subsequent existence and relativization work.
4. Montagna and Di Paola–Montagna's syntactic examples, with the precise
   uniform equality relation and their failure of local connectedness.
5. The motivation for a comparison functor to a suitable target instead
   of assuming local connectedness of the syntactic source.
6. The range-functor inseparability theorem, its lifting condition, and the
   counterexample showing why that condition matters.

The current bibliography contains Di Paola–Heller, Montagna,
Di Paola–Montagna, the author's LOC note, Bernardi, and the three-point
note. It has no Rosolini, Heller-existence, Lengyel-2004, or foundational
restriction-category entry. Merely inserting these names into a citation
cluster would not supply the missing comparison. Each included work needs
one sentence explaining its relevant hypothesis, construction, or
limitation and the connection to the present application.

Attribution requires care. The corrected Lengyel-2004 existence theorem
has a **faithful iteration functor** hypothesis; it must not be described
as an existence theorem for arbitrary range functors. The present
range-functor lifting theorem and the earlier iteration-based existence
theorems have different hypotheses and tasks. The literature comparison
must use the corrected source. The source-checking work for those claims
belongs to the primary-source review; this audit establishes their absence
from the baseline and the comparison that must be made.

The LOC Introduction also distinguishes the valid unprimed syntactic
categories from the failed pointwise-provability quotients. If the revised
literature discussion introduces the primed systems, it must retain that
distinction and cite the composition obstruction. Introducing those systems
is not necessary merely to restate the already-precise unprimed definition.

## Recommended outline before rewriting

Use a genuine introductory literature narrative and an early terminology
section. A conservative revision can retain most of the proof order:

1. **Introduction.** Explain the incompleteness problem; review the
   Di Paola–Heller, Rosolini, Heller, syntactic-category, and corrected
   existence-theorem context; state what the inherited local-connectedness
   theorem requires; identify the two present applications and their
   additional effective steps. End with the roadmap.
2. **Categorical preliminaries.** Move restriction notation, domains,
   ranges, products and coproducts, sections, partial monomorphisms,
   splitting, weak choice, connectedness, local connectedness, range
   functors, and the adopted recursion-category terminology here. Give
   the total-parameter property of the Turing morphism.
3. **The syntactic categories.** Define numerical types and the uniform
   proof quotient; verify the operations using the already-stated language.
4. **Interpretation in models.** Retain the single-model construction.
5. **A faithful family and theory extension.** Retain the model-family
   theorem and commuting square, without inserting basic definitions here.
6. **The range-functor inseparability theorem and syntactic lifting.**
   Retain the local-connectedness section construction and application.
7. **Effective arithmetic observations.** Retain the actual application
   through `Rec→Pfn`, the proof/refutation inclusions, and the incompleteness
   conclusion.
8. **Computable fork diagrams and proof observations.** Retain the three
   substantive subsections, but explain the diagram objects before
   “endpoint,” the syntax before “atom map,” and the allowed extension
   class before its theorem.

This proposed additional preliminary section has a specific purpose: it
removes the need to learn the theorem's vocabulary inside its applications.
It is not a request to lengthen every definition or repeat all background
in the Introduction.

## Proposed abstract

The following is a replacement proposal, not a claim that every editorial
choice has already been implemented:

> A recursively inseparable pair consists of two disjoint computably
> enumerable sets with no recursive separator. We apply a categorical
> inseparability theorem based on local connectedness: partial maps are
> determined by their restrictions to domains having no disjoint nonzero
> decomposition. For each consistent extension `T` of Peano arithmetic,
> we interpret programs identified by uniform `T`-provable equality in
> all countable models of `T`. A single `T`-provably total program realizes
> each choice between two predicates that `T` proves disjoint and exhaustive.
> For computably enumerable `T`, the theorem's numerical instance gives
> a fixed recursively inseparable pair contained in the corresponding
> proof and refutation sets. This yields essential
> incompleteness of Peano arithmetic. A second application treats diagrams
> `Y_1←Y_0→Y_2` of computably enumerable sets and computable maps. We
> construct a classical propositional presentation in this category and
> prove that every consistent computably enumerable rule-closed subdiagram
> of formulas extending it is incomplete, by projecting to either outer
> component.

This proposal omits the symbols and implementation labels `S_T`, “split
restriction category,” “range functor,” “endpoint evaluation,” “Turing
morphism,” and “atom map.” Their mathematical content belongs in the
Introduction and preliminaries. It retains the relevant class of extensions
in the second application rather than claiming incompleteness for arbitrary
external subobjects or arbitrary extensions.

## Priorities and next review

1. Settle the mathematical and literature outline before composing more
   introductory prose.
2. Rewrite the abstract against its own first-use inventory; later
   definitions do not satisfy the author's present abstract requirement.
3. Supply the missing literature comparison from checked primary sources,
   especially distinguishing faithful iteration functors from range
   functors and the original source assumptions from target assumptions.
4. Move the basic definitions forward and define the currently absent
   terms used as theorem hypotheses.
5. Read the renamed complete source in order, repeat the term inventory,
   and then submit that actual version to the hostile mathematical review.

No manuscript or PDF was changed for this initial audit. No compilation or
new mathematical certification is claimed. Earlier proof verification
remains separate; the defects recorded here concern exposition,
definition order, and the requested comparison with prior work.
