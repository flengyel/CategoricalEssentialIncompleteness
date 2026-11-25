# Appendix D referee and writing review

The two numbered results and the intervening arguments were read in the order of the four parts of Appendix D: the faithful model family, inseparable pairs under theory extension, numeral observations and true arithmetic. The independent reader reconstructed the arguments from v90 before comparing them with the Lean sources, then checked the revised text. Appendix D was byte-identical at the reviewer’s v89 commit and on v90. [Reviewed v91 manuscript](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6f8ca9ed5ee9d4e2c3596420c7819da928029a41/manuscript/latex/appendices/d-faithful-family.tex) · [Independent review](INDEPENDENT.md)

## A. Mathematical blockers

None found in Appendix D. In Theorem D.1, if two program classes differ, their universal graph-equivalence sentence is unprovable in $T$. A model of its negation can be taken on the carrier of natural numbers. Its coordinate distinguishes the two morphisms. Testing partial functions on singletons detects equality of both domains and values.

## B. Major weaknesses

The v90 correspondence table described numeral observations under theory extension as equal. The manuscript gives $E_T(c)\subseteq E_{T'}(\mathsf{quot}_{T,T'}c)$, since every proof in $T$ is a proof in $T'$. The Lean theorem proves that inclusion. The v91 table now states it. The comparison square itself commutes as an equality of functors. [Corrected table](../../../FORMALIZATION_STATUS_V91.md) · [Observation inclusion](../../../Lean/CategoricalEssentialIncompleteness/V46ManuscriptPassageApplicationsChecks.lean#L67) · [Strict square](../../../Lean/CategoricalEssentialIncompleteness/SyntacticFamilyExtension.lean#L76)

## C. Notation and exposition

Theorem D.1 states the graph-equivalence sentence directly. $E_T$ denotes the observation map. Corollary D.2 writes $\omega$ throughout, and $\mathsf{quot}_{T,T'}$ denotes the quotient functor in the square and its applications. The appendix label is `app:faithful-family`. The proof of range preservation identifies the same formula $R_e$ in either theory.

## D. Consistency with the cited result

Di Paola and Montagna’s Corollary 4.4 is stated on p. 657 and its proof ends on p. 658. It covers the unprimed $S_T$ for every consistent c.e. extension of PA. The proof considers both cases of $\Sigma_1$-soundness. Theorem 4.5 on p. 658 concerns the primed construction. The manuscript's application to true arithmetic invokes its own Corollary D.2 on inseparable pairs, whose hypotheses permit non-c.e. theories. [Primary-source check](CITATION.md) · [Corollary D.2 in Lean](../../../Lean/CategoricalEssentialIncompleteness/V46SyntacticExtension.lean#L78)

## E. Verification

The rebuilt paper has 102 pages. All 161 labels have the same numbers after the single label rename. The 26 archive entries match the sources byte for byte. The manuscript verifier and six axiom-parser tests passed. [Paper](../../../manuscript/logical_consequence_and_essential_incompleteness_v91.pdf) · [Manifest](../../../MANUSCRIPT_CURRENT.json)

## F. Scope

No mathematical error or open Lean obligation was found in Appendix D. The review compared the printed assertions with the Lean proof sources. The Lean tree, verifier and dependency pins match v90. The last full kernel replay tested v84. [Kernel report](../../V84_WSL2_LEAN_VERIFICATION.md)
