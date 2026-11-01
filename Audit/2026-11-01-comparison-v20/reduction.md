# Assessment of the three reviews — manuscript v20

Manuscript: *Logical consequence and essential incompleteness in recursion categories*, version 20, 61 pages, commit `c182b1b2c54af499e0ef6f3f7ae6f179eaa55b65`.

## Verdict and location of the comparison theorem

The new comparison theorem is **Theorem 3.1, p. 5**, in its own subsection, **§3.1, “The comparison theorem.”** The containing **§3, “Diagonal comparison and lifted partial conditionals,” pp. 4–7**, also constructs the locally connected target conditionals and proves source inseparability. **§4, pp. 7–10**, applies the comparison to internally generated sentence theories. This organization is adequate; no additional section is needed merely to isolate Theorem 3.1.

The independently checked diagonal argument and the new internal-theory implication have no confirmed mathematical blocker. This judgment concerns those proofs and their stated dependencies, not the correctness of every retained theorem or every literature attribution. The substantial remaining task is to instantiate the new semantic-consistency theorem in the concrete arithmetic development. That work is in the approved plan but is not yet in the paper. Version 20 was a first installment of that revision, so this is unfinished implementation rather than a contradiction in the theorem as stated.

The hostile referee, outliner, and mathematical-writing reviewer reached compatible conclusions. Their agreement is supported by the source calculations below; it is not being used in place of checking them. No manuscript file was changed during this review.

## Results and dependencies checked independently

| Result | What the written argument establishes | Assessment |
|---|---|---|
| Theorem 3.1, p. 5 | Applying the Turing property to \(b^{-1}\ell\pi_2\) gives total \(g\). The equality \(hg=\ell g\) implies equality of the two target inverse images; their disjointness makes both zero. Nontriviality and preservation of the indicated join then exclude coverage. | The types and equalities check. The proof neither transports a product through \(F\) nor assumes that \(\ell\) is total. |
| Proposition 3.4 and Theorem 3.5, pp. 6–7 | Local connectedness, splitting and weak choice provide the partial section and its two inverse-image equations. A hypothetical source separator gives the target data forbidden by Corollary 3.2. | These results genuinely use the new comparison. The local-connectedness argument is a sufficient lifting construction, not a hypothesis hidden in Theorem 3.1. |
| Theorem A.5, Theorem A.6 and Lemma A.7, pp. 47–49 | Initial derivations give a least closed formula image; pullback gives its sentence part; a partial inverse of the image mono identifies that image with the range. | The image/range hypothesis is essential to the stated identification and is retained in §4.1. Numerical realization proofs belong in the application sections. |
| Extension \(\widehat F\), p. 8 | The chosen splittings define the functor on objects and morphisms; the receiving-idempotent calculation proves range preservation; the explicit coproduct comparison gives coproduct and join preservation. | The object and morphism types are explicit, including the identification of original source objects with their identity splittings. |
| Proposition 4.1, pp. 8–9 | A factorization of the interpreted sentence-conclusion morphism through a chosen validity subobject puts its range inside that subobject. Disjointness from its negated inverse image then gives interpreted consistency. | A conditional transport statement. It does not itself construct the validity subobject or prove soundness of a concrete interpretation. |
| Theorem 4.2, p. 9 | Theorem 3.1 applied to the two interpreted theorem/refutation domains gives avoidance. Pullback excludes target coverage; preservation of joins excludes source coverage. | Both conclusions follow. No reflection of consistency is asserted or needed. |
| Corollary 4.3, p. 10, and the retained applications | A separator of a consistent enlargement would pull back to a separator of the original inseparable pair. The Miller, arithmetic and cosheaf applications use this result. | The existing applications remain connected to Theorem 3.1 through Theorem 3.5. They do not yet instantiate Theorem 4.2. |

The actual application chain is

\[
\text{Theorem 3.1}\longrightarrow\text{Corollary 3.2}
\longrightarrow\text{Theorem 3.5},
\]

where Proposition 3.4 supplies the target section and the application sections supply the required lifts. Theorem 3.5 supplies the inseparable pairs; Appendix A and its realizations supply the theorem subobjects; Corollary 4.3 and the concrete reductions give the incompleteness conclusions. The other branch leads from Appendix A and Theorem 3.1 to Proposition 4.1 and Theorem 4.2. Its concrete soundness factorization and arithmetic partial-proof-search application still have to be supplied.

## Disposition of the reviewers’ findings

| Finding | Disposition after checking | Required treatment |
|---|---|---|
| Placement of the comparison theorem. | All three reviews correctly locate its dedicated subsection and the separate general-theorem section. No organizational gap is established. | Keep §§3–4 in their present relationship. A shorter §3 title is optional. |
| Theorem 4.2 has no later concrete invocation. | Confirmed by reading the application proofs and the source references. This is an incomplete revision step, not a defect in the conditional theorem. | Complete the model/soundness section and the arithmetic application. Do not describe that route as already implemented. |
| Distinction between graph interpretation and soundness of the interpreted proof object. | Accept the reviewers’ distinction. Proposition 4.1 explicitly requires the factorization. Proposition 7.1 proves graph-interpretation preservation, which is a different statement. The manuscript does not conflate them. | Preserve the distinction and prove the additional factorization where it is used. |
| The all-model family has a remaining use despite its dispensability for Theorem 3.5. | Confirmed. Faithfulness is unnecessary for that particular application, but is used in §9.1, equation (16), p. 34. The reviewers correctly recommend preserving this dependence. | Move the faithful-family construction and its observation argument together to the planned Appendix D, or retain the necessary reference if they are separated. |
| Different parts of §9.1 have different later uses. | Confirmed. The definition of \(\operatorname{Pair}(\mathrm{Rec})\) is used by Theorem 10.5, whereas the observation equivalence needs faithfulness. | Keep that definition available before its use. Preserve the complete-ambient-theory example’s distinction between computational inseparability and incompleteness of the ambient theory. |
| “Admissible domain monomorphism” in Propositions 5.5 and 9.1 needs clarification. | Accept as a local terminology correction. The proofs establish the precise partial-inverse property. The two ambient-category statements require different wording because one is an identity and the other an equivalence. | Use the typed replacements below when these sections are revised. This is not a failure of their proofs. |
| Appendix B’s defined “total restriction embedding” duplicates “restriction monomorphism.” | Accept only as optional terminology unification. The term is defined, so it is not a missing-definition defect. | If changed, retain the equations and change the subsequent occurrences consistently. |
| Theorem 3.1 assumes more structure than its diagonal calculation uses. | Accept only as an available weakening. The range-functor setting serves the later theory construction; extra hypotheses do not invalidate the result. | No required edit. Do not delay the concrete application to broaden the theorem unnecessarily. |
| “Actual sets” and “actual domain” are dispensable; some numerical regularity proofs overlap. | Accept the two adjective deletions as minor prose economy. Treat proof consolidation as optional and lower priority. | Preserve the distinctions between object terms and sets, and between a declared source and a domain of definition. Do not remove Appendix B’s additional naturality/descent argument. |
| The introduction’s roadmap and appendix order are stale. | Confirmed, but explicitly deferred by the author. | Revise the introduction and abstract last. Their unchanged wording is not permission to rewrite them during this review. |

The mathematical-writing report’s two important replacements are correctly typed:

1. In Proposition 5.5, \(\mathcal D_a=\operatorname{Tot}(\operatorname{Split}(\mathcal E_a))\) by definition. Write: “Every monomorphism of \(\mathcal D_a\) has a partial inverse in \(\operatorname{Split}(\mathcal E_a)\).”
2. In Proposition 9.1, \(\mathcal C_{\mathrm{rec}}\) is equivalent to the total splitting, not literally that category. Write: “Under the displayed equivalence, every monomorphism of \(\mathcal C_{\mathrm{rec}}\) corresponds to a restriction monomorphism in \(\operatorname{Split}(\mathrm{Rec})\).”

Replacing the second statement by a claim that its monomorphisms already belong to the restriction splitting would suppress a categorical identification that has not been made. The submitted writing report avoids that mistake.

## Recommended next work

1. Complete the model-interpretation and soundness section. Specify the represented axiom presentation, its sentence-proof object, the interpretation, the validity subobject, and the factorization required by Proposition 4.1. Keep the ambient arithmetic theory distinct from the represented theory. Develop the planned ultrapower comparison with its stated preservation properties.
2. Rewrite the arithmetic application in the fixed ambient syntactic category. Prove the diagonal-domain reductions and the partial proof-search lift, then invoke Theorem 4.2 explicitly. Retain the numerical realization and the ordinary recursive-inseparability conclusion.
3. Move the faithful-family comparison and the arguments requiring faithfulness to Appendix D, preserving the other dependencies noted above. Move the one-model conditional-lifting argument into the model section.
4. Put Miller after arithmetic, as the approved plan proposes, and retain the cosheaf application. Keep the full realization and substitution proofs; the plan’s shorter outlines are not replacements for them.
5. Apply the small terminology corrections while revising those sections. Update the introduction and abstract after the mathematical body has reached its intended form.

## Review limits

This assessment read all three complete reports and checked their principal claims against the written §§2–4, the rule-closure and image/range arguments of Appendix A, the syntactic-theory statement, the model and faithful-family sections, and the later application statements and proof dependencies. It independently checked the central diagonal and interpretation arguments. It did not independently re-prove every numerical construction, the entire cosheaf construction, or every cited external result, and it makes no novelty certification. The writing report’s minor page-range errors were corrected before consolidation: Appendix B occupies pp. 50–58; Appendix C occupies pp. 58–60; the deferred roadmap passage is on p. 2.

No mathematical correction to Theorem 3.1 is warranted by the evidence from this review. The next substantive advance is its concrete use through Theorem 4.2, with the soundness and lifting premises proved in the application.
