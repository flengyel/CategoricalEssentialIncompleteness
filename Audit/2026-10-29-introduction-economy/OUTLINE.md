# Introduction economy: initial outline and revised structure

## Revised structure and current status

The initial plan below predates source edits and is retained as the
review record. The reviewed Version 2 source is now
`manuscript/essential_incompleteness_via_local_connectedness_v2.tex`,
SHA-256
`cae09d2ed4cb0d9606eb7973ddfb4143fcd4736e7ccc3e0e8dd6c177248993b1`.
Its Introduction has seven paragraphs and approximately **634 prose
words**, a **46.0% reduction** from 1,174 using the same counting method.
The detailed final prose review is in `WRITING_REVIEW.md`.

The final actual structure is:

1. **Introduction:** DPH purpose and separation obstruction; relevant
   history; target local connectedness and the selecting-map lift;
   syntactic model-family construction; separate effective arithmetic
   step; nonnumerical application; roadmap.
2. **Categorical preliminaries:** partial maps and domains; products,
   coproducts and local connectedness; recursion categories.
3. **The syntactic recursion category:** uniform graph equality and
   composition; the relocated pointwise-quotient comparison.
4. **Interpretation in models:** the object and arrow actions of each
   interpretation functor and their preserved structure.
5. **A faithful family and theory extension:** the product target,
   faithfulness, and the extension square.
6. **Switching and the local-connectedness theorem:** the target
   construction; the fully stated lifting theorem; the sufficient
   disjoint-arrow-join criterion; syntactic lifting.
7. **Effective observations and essential incompleteness:** the numerical
   theorem instance, finite computations, proof/refutation inclusions,
   separator pullback, and the relocated precompleteness comparison.
8. **A recursion category from a three-point space:** the exact numerical
   diagram category; local connectedness and lifting; endpoint functors;
   proof observations and the explicitly defined extension class.
9. **Appendix A:** cosheaves and numerical diagrams; partial maps,
   ranges and connected domains; universal object and frames; Turing
   morphism; recursion category and its splitting.
10. **Appendix B:** finite syntax and proofs, including the concrete
    proof carrier, theorem domain and consistency argument.
11. **Appendix C:** necessity example for the statement with section
    lifting omitted. The theorem in the body retains the hypothesis.

All earlier mathematical proofs remain; the shorter previews do not
remove material imported from the private notes. The general range
functor still has no product-preservation requirement. The typed
coproduct comparison is now explicit throughout.

**New substantive steering:** the author has reopened whether the
paper derives essential incompleteness from the intended recursion-
category construction, rather than proving the arithmetic application
through a separate classical numerical instance. The prose review does
not settle that issue. Publication and the abstract's dependency claim
remain paused for the mathematical review. The initial plan's separate
arithmetic paragraph must not be mistaken for approval that the desired
general categorical goal has been achieved.

## Original pre-edit plan

**Expanded review scope.** The author subsequently requested a line-by-line
prose audit of the entire active manuscript, not only the Introduction.
The review now covers antecedents, the mathematical content of local
labels, definition order, named and typed comparison maps, the precise
lifting hypothesis, and carrier-relative computability throughout §§1–8,
Appendices A–C, the abstract, and bibliography. The original shortening
plan below remains the plan for the Introduction. Whole-paper findings
and concrete repairs are recorded separately in `ANTECEDENT_REVIEW.md`.

Baseline: repository main `c5533a6`,
`manuscript/essential_incompleteness_via_local_connectedness.tex`.
Source SHA-256:
`99b760671b51bafe038fa371ca9814d9de55dd53b8099487a3d6d8d44f73bc21`.
The complete Introduction and the relevant definitions and applications
in §8 and Appendix A were read. This is a focused editorial plan, not a
new review of every proof. The mathematical source has not been edited.

The mathematical-writing plugin and the supplied Knuth–Larrabee–Roberts
Section 1 excerpt govern the review. The applicable verified advice is to
motivate what follows (12), maintain connected prose (10), introduce
variables with complementary explanations (11), keep prose intelligible
when formulas are skimmed (13), and avoid ambiguous reading (17). These
principles support changing the order and removing duplicated previews;
they do not require removing mathematical proofs or historical antecedents.

## Diagnosis and actual outline

The Introduction currently has about **1,174 prose words in twelve
paragraphs**, excluding subsection headings, citation/reference commands,
and inline mathematics. This is a reproducible approximate prose count,
not a TeXcount total. A 40% reduction gives a target of about **700 prose
words** by the same method.

The motivating implication is in the second paragraph, after a paragraph
that already introduces restriction idempotents, Rosolini's framework,
selected monomorphisms, ranges, and coproducts. The reader receives the
machinery before the reason to study it. Later, the 170-word theorem
preview repeats the target hypotheses defined in §2 and stated in §6.
The arithmetic result is then explained twice: through the abstract
obstruction and through the later proof/refutation paragraph. Some
complementary explanation is useful, but the present allocation is longer
than the argument requires.

| Current paragraph | Approximate words | Function and recommended treatment |
| --- | ---: | --- |
| §1.1, Di Paola–Heller/Rosolini | 106 | Keep the DPH purpose in the opening. Move or remove the repeated technical definitions; retain Rosolini in the compressed history. |
| §1.1, separation obstruction | 94 | Move its motivation to the opening and combine it with the DPH purpose. |
| §1.1, Bernardi | 92 | Keep the relevant antecedent in one sentence; move the numerical precompleteness explanation and fuller comparison to the end of §7 if retained. |
| §1.2, connected domains | 80 | Retain the short connected/local-connected explanation at the point where comparison with a target is motivated. Leave formal complement and separation definitions to §2. |
| §1.2, Heller/Lengyel | 88 | Retain the relevant existence-theorem history, including the original near-product qualification and paired errata citation. Compress proof-mechanism commentary. |
| §1.2, range theorem and lifting | 170 | Keep the range-functor action and selecting-map lift. Omit the list of splitting/weak-choice/inverse-image conditions here; those remain fully stated and proved in §6. Keep brief internal references to the criterion and counterexample. |
| §1.3, `S_T` | 90 | Combine uniform program equality, failure of source local connectedness, and motivation for the target construction. |
| §1.3, primed systems | 108 | Keep one sentence excluding the pointwise-provability quotient, with the Composition citation. Move the detailed `S′`, `S′_T`, DPM soundness qualification and composition comparison to §3. |
| §1.3, model-family result | 92 | Combine with the `S_T` paragraph, retaining the faithful locally connected product target and the single selecting program. |
| §1.3, arithmetic conclusion | 92 | Keep a separate concise paragraph: numerical inseparability plus finite computations and c.e. proofs, hence essential incompleteness. Preserve its distinction from semantic faithfulness. |
| §1.3, three-point application | 98 | Replace the undefined “computable diagrams” with the actual carrier and arrow data; state the nonnumerical result and effective-extension conclusion. |
| Roadmap | 64 | Reduce to two sentences grouping setup, theorem, applications and appendices. |

The current three subsections are not essential to the shorter
Introduction. Seven connected paragraphs without subsections would give
the argument room to develop without turning each transition into a new
heading. Keeping subsection labels is an optional presentation choice,
not a mathematical requirement.

## Proposed argument and word allocation

1. **Problem and obstruction, about 95 words.** Begin with the DPH aim
   and its concrete obstruction: if proofs and refutations contain a
   recursively inseparable pair, completeness would decide a separator.
   Name essential incompleteness. The reader now knows what the category
   is meant to explain.
2. **Relevant antecedents, about 120 words.** Rosolini supplies the
   partial-map framework; Heller supplies the local-connectedness
   existence argument; Lengyel 2004 uses faithful iteration-preserving
   functors without requiring near-product preservation; Bernardi supplies
   an established inseparability approach through provable program
   equivalence. Retain the paired original/errata citation and avoid
   portraying the near-product qualification as a correction.
3. **Why a comparison target is needed, about 110 words.** Define `S_T`
   by uniform provable graph equality, state that consistent c.e. `S_T`
   is not locally connected, and explain the model-family functor into a
   product of partial-function categories. Give the concise connected-
   domain meaning here. Exclude the primed pointwise quotient in one
   sentence, with its citation; put its fuller account in §3.
4. **The lifting mechanism, about 125 words.** Explain what the range
   functor preserves and why a selecting map matters. The target
   constructs it from complementary source domains; the lifting
   hypothesis returns it to a source arrow, where Turing universality
   gives the contradiction. State that the one provably total program
   realizes this selection across all models. Refer briefly to the
   sufficient criterion and Appendix C; the actual theorem retains
   lifting.
5. **The effective arithmetic step, about 70 words.** Explain the
   separate numerical instance, PA proofs of finite computations, and
   proof/refutation inclusions for every consistent c.e. extension.
   Do not suggest that semantic faithfulness alone yields incompleteness.
6. **The nonnumerical application, about 110 words.** Specify the fork
   carriers and arrows exactly. State their cosheaf interpretation, the
   nonnumerical recursion category, the endpoint observations, and the
   conclusion for the defined effective class of extensions.
7. **Roadmap, about 35 words.** Group §§2–5 as setup/representation,
   §6 as the theorem, §§7–8 as applications, and the appendices as the
   detailed constructions and necessity example.

This allocation totals about 665 words and leaves modest room for
transitions and exact qualifications while staying close to 700. It is a
budget, not a demand to delete a necessary hypothesis to reach a number.

## Precise terminology repair

“Computable diagram” is not defined by the current Introduction or
abstract. It should not serve as a name for the categorical objects at
issue, nor be confused with the established model-theoretic phrase.
No excursus on the latter notion is needed. Use the actual category and
data already specified in §8.

Recommended introductory formulation:

> The second application uses forks `Y_1 ← Y_0 → Y_2` whose carriers
> are computably enumerable subsets of finite powers of the natural
> numbers and whose arrows are partial recursive functions total on
> their source carriers.

The next sentence can explain that their underlying set-valued diagrams
determine cosheaves on the specified three-point space. Do not imply that
the cosheaf's value at every open has an injective numerical presentation:
Appendix A correctly constructs the largest value by a quotient pushout.

In §8, retain the existing category definition:

> Let `C_rec` have c.e. subsets of finite powers of `N` as objects and
> partial recursive functions total on their sources as arrows, with
> extensional equality. Put `E=C_rec^J` for `J=(1←0→2)`.

Then call an object a **diagram in `C_rec`**, a **diagram of shape `J`**,
or simply **an object of `E`**, as the context permits. Its morphisms
are commuting triples of arrows in `C_rec`. This also avoids reading
“total recursive component map” as requiring an extension total on the
whole ambient numerical space rather than total on its specified carrier.

Corresponding local replacements outside the Introduction are:

- Abstract: replace “using computable diagrams on a three-point space”
  with a brief description of forks of c.e. numerical carriers and partial
  recursive maps total on their carriers. The abstract should not add
  another undefined label in place of the old one.
- §8: replace “The computational diagrams form…” by “Put
  `E=C_rec^J`…” and retain the explicit object/morphism actions.
- Appendix A.1: use “For `Y∈E`…” and “A morphism in `E` acts…” in
  place of “computational diagram” and “computational diagram map.”
- Lemma on frames: use “isomorphisms in `E`” or “diagram isomorphisms
  with recursive components,” avoiding the loose collocation “computable
  diagram.”
- Appendix B's title can say “Finite syntax and proofs in the diagram
  category” or name the three-point category. Its first paragraph already
  specifies `E` and its carriers.

These changes leave the category, its morphisms, and all universal
properties unchanged. They do not replace the construction by a category
of arbitrary set-valued cosheaves or alter the computational domains.

## Material preserved by relocation

The shortening concerns the Introduction and terminology. Every proof in
the main body and Appendices A–C remains. In particular, retain the
disjoint-arrow-join criterion, the lifting hypothesis, the counterexample
to the statement with that hypothesis dropped, the full compatible Turing
morphism, exact-domain parameterization, finite syntax/proofs, and
consistency argument. Private-source mathematics already incorporated
must not disappear with its introductory preview.

The detailed primed/unprimed comparison belongs immediately after the
uniform graph-equivalence definition in §3. The precompleteness comparison
can accompany the existing Bernardi paragraph at the end of §7. The
formal definitions of restriction idempotents, complements and the full
target hypotheses already have appropriate homes in §§2 and 6, so their
introductory repetitions can be shortened without losing them.

After the rewrite, compare the new introductory word count using the same
method, check every remaining specialized term at first use, verify the
history and source/target direction, and reread the modified §3, §7, §8 and
appendix anchors. This focused plan does not claim a new proof audit or
build verification.
