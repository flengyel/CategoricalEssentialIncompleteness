# Version 44 comparison passage: author-side hostile review

Scope: the first two paragraphs of related work, the referenced interpretation proposition and logical comparison theorem, the arithmetic interpretation functor, and Appendix D's product target. No manuscript edits or whole-paper judgment.

## (A) Kill-shots / hard blockers

None established. The passage names the functor, its domain and codomain, its extension, and the logical role of the comparison. It does not assume that the target is a recursion category or that it contains an inseparable pair.

## (B) Major weaknesses

Anchor: related work, “Soundness supplies disjointness of the interpreted theorem and refutation restriction idempotents.” Failure mode: unproved as stated. Evidence: derivation. Proposition 4.1 uses soundness to factor the interpreted conclusion morphism through a validity subobject. To deduce disjointness of the theorem and refutation restriction idempotents, it also assumes that validity is disjoint from its inverse image under negation. Soundness alone does not give that condition for an arbitrary interpretation. Downstream impact: the stated input to Theorem 4.2 is not established by the sentence as written. Severity: major but local and repairable. Suggested replacement: “For the semantic interpretations of Proposition~\ref{prop:interpreted-theory}, soundness and incompatibility of validity with negation give disjointness of the interpreted theorem and refutation restriction idempotents.” The original introduction's earlier construction paragraph already states this condition correctly.

## (C) Minor issues

Anchor: related work, the Appendix D target “indexed by arithmetic models of the theory defining the syntactic category.” Failure mode: ambiguous indexing scope. Evidence: citation to Appendix D's opening definition. The defined index set consists of models with underlying set $\N$. Omitting that restriction leaves an apparent index by all arithmetic models, with no fixed carrier bound. Repair: add “with underlying set $\N$”. No new symbol for the index set is needed in the introduction.

## (D) Cross-section consistency failures

The displayed types match the body: $F:\mathscr R\to\mathcal A$ has recursion-category domain and split restriction-category codomain in the logical application; $\widehat F:\Split(\mathscr R)\to\mathcal A$ interprets the sentence theory. Theorem 4.2 obtains both $t\vee(\widehat F\nu)^*t\ne1$ in $\mathcal A$ and $t_A\vee\nu^*t_A\ne1$ in $\Split(\mathscr R)$, under its full hypotheses. This is an incompleteness comparison, not a transfer of target inseparability.

For the main arithmetic application, $F_M:S_{\PA}\to\Pfn$ is the program-graph interpretation for standard arithmetic or an arithmetic ultrapower. The family comparison in Appendix D instead uses $F_T:S_T\to\prod_{M\in\mathcal M_T}\Pfn$, with the set $\mathcal M_T$ specified there. The passage's stated roles agree with these constructions after the qualification in (C).

## (E) Acceptance conditions, non-negotiable

1. Qualify the soundness-to-disjointness sentence by validity's incompatibility with negation. Endpoint: the revised related-work passage agrees with Proposition 4.1 and does not suggest soundness alone supplies the required disjointness.
2. Specify that the Appendix D model index has carrier $\N$. Endpoint: the introduction's product target agrees with Appendix D's defined set of indices.

These are local changes; neither requires reconstruction of the comparison theorem. Verify the revised source's references and rendered passage before delivery.

## (F) Not checked / uncertainty log

No fresh audit of the comparison proof, arithmetic coding, or the other application proofs was performed. Only the stated dependencies and types relevant to the new passage were checked. Strongest confirmed blocker: the unqualified soundness-to-disjointness implication in (B). Strongest suspected unconfirmed blocker: none identified in this passage. Most important thing not checked: all body proofs. This recommendation does not depend on unavailable material. Final recommendation: unknown for acceptance of the whole paper; the specified local corrections are required for this passage.

## Resolution in the final version 44 source

Reinspection of the revised related-work passage confirms both required corrections. The soundness sentence now explicitly assumes that the validity subobject is disjoint from its inverse image under negation and cites Proposition 4.1. The arithmetic model $M$ is introduced before $F_M:S_{\PA}\to\Pfn$, and the target category is named. Appendix D's theory $T$, model family $\mathcal M_T$ with underlying set $\N$, and product-valued functor $F_T$ are now introduced and typed in the passage itself. The two types of model interpretation remain distinct, and no target inseparability or target recursion-category assumption has been inserted.

No remaining finding is established in these final paragraphs. The earlier findings in (B) and (C) are resolved; the whole-paper recommendation remains outside the scope of this review.
