# Version 38 abstract and introduction: scoped mathematical review

Scope: the revised abstract and introduction before the unchanged Related work subsection. Summaries were compared with Appendix A, §§3–4 and the relevant realization/application statements. This was not a fresh audit of all body proofs or historical sources.

The final installed abstract and introductory text before Related work were reread continuously after the local corrections. The image paragraph's revised final sentence accurately identifies the generated sentence theory as the sentences derivable from the chosen axiom subobject under the internal rules. No additional finding arose.

Final source SHA-256 values:

| Source file | SHA-256 |
| --- | --- |
| `abstract.tex` | `16f51866ca73f2ee5294da84808300811c5673877c83b47719114e3bf8bf17ef` |
| `sections/01-introduction.tex` | `962bef8e77710b3a4e7bfc3e96d6db2f2314290945da74d85ca62490b78f0e30` |

## (A) Kill-shots / hard blockers

None found.

## (B) Major weaknesses

None found.

## (C) Minor issues

Three local scope/citation issues were identified and corrected during the review:

1. **Abstract, sentence beginning “Reductions of inseparable pairs”: extension class.** The first draft said incompleteness persists under consistent extensions without the effective/represented restriction. Failure mode: **ambiguous**; evidence: **counterexample** and Corollary 4.3. An unrestricted assertion would include complete consistent non-effective extensions, whereas Corollary 4.3 concerns represented theories. The installed text now says “Total reductions of inseparable pairs give incompleteness for consistent extensions in the specified effective classes.” The concrete classes are stated in the following application summaries. Resolved.

2. **Introduction, first incompleteness argument: target category.** The initial draft introduced only a split restriction target before invoking the validity-subobject consequence of Proposition 4.1. Failure mode: **missing_definition/ambiguous scope**; evidence: **manuscript statement**. The cited implication requires a target that is the partial-map category of a regular category. The installed text now expressly supplies that qualification, followed by disjointness of validity from its inverse image under negation. Resolved.

3. **Introduction, lifting counterexample sentence: phenomenon attributed to Appendix C.** The initial draft cited Appendix C for sending an inseparable source pair to a separable pair. Failure mode: **misuse_of_prior_work** (here an internal cross-reference); evidence: **manuscript statement**. Proposition C.1 instead constructs a diagonal pair already separable in the source when the lift is absent. The installed sentence now states exactly that the diagonal pair can be separable even for a faithful range functor preserving restriction products and reflecting zeros. The distinct loss-of-inseparability phenomenon remains in the Miller discussion. Resolved.

No further concrete mathematical or typing finding remains in the installed text examined.

## (D) Cross-section consistency failures

None remaining. The revised exposition agrees with these body results:

- **Appendix A.5–A.6 and §4.1:** the chosen axiom subobject determines the inference algebra; the regular image of the sentence-conclusion morphism is the generated sentence theory. The introductory objects and morphisms have the stated types in the regular category \(\mathcal D=\operatorname{Tot}(\operatorname{Split}(\mathscr R))\).
- **Lemma A.7:** the partial-inverse hypothesis is retained when the image is identified with a restriction range. Sentence negation gives the refutation domain; the consistency and completeness equations match §4.1.
- **Proposition 4.1 and Theorem 4.2:** the soundness factorization, validity-disjointness condition, total reduction, and partial-conditional lift remain distinct ingredients.
- **Corollary 4.3:** the second route retains a fixed inseparable pair, a total reduction, growth under axiom inclusion, and consistency of the represented extension. The abstract does not need to reproduce this proof architecture.
- **Theorem 5.9 and §7:** the syntactic realization uses universal provable graph equality; the arithmetic application fixes \(S_{\mathrm{PA}}\) while varying represented axioms. The interpretation of codes in standard arithmetic is distinguished from interpretation of the decoded formulas in a model of those axioms. Uniform independent sentences and arithmetic-ultrapower transport retain their actual scopes.
- **Theorem 8.6:** the Miller extension class retains one oracle program semideciding the same axiom set from every binary representation. First-order logic with equality and the reduction from the two cut domains are correctly described.
- **Corollary 9.6:** the cosheaf application is propositional and produces two endpoint theories, each incomplete under every consistent same-language extension with a c.e. axiom set.

## (E) Acceptance conditions, non-negotiable

The three local corrections are present in the installed source. No additional review round is required for these passages on the evidence examined.

## (F) Not checked / uncertainty log

The unchanged Related work subsection, full body proofs, bibliography, compiled pagination, and visual layout were not re-audited. Strongest confirmed blocker: none. Strongest suspected blocker: none within the checked scope. Most important unchecked material: a fresh complete body-proof audit, outside this task. The findings do not depend on unavailable material. Final recommendation on the whole manuscript: **unknown**; the revised abstract and introductory account have no remaining concrete mathematical or typing objection from this scoped check.
