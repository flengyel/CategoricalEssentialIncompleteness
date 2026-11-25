# Appendix A referee and mathematical writing review

The review covered §§A.1–A.6 and their uses of the revised notation elsewhere in the paper. The referee reconstructed the arguments from the v88 manuscript, compared them with the Lean declarations, and read the revised v89 text. Separate readers checked the categorical deletion and substitution proofs and the cross-references in §§4, 6, 7 and 10. The review found one valid inference left implicit in v88. It found no mathematical error or open Lean obligation in Appendix A. [Reviewed manuscript at `31c6441`](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/31c64416f69720e520febd3d4153eb4fce2b0403/manuscript/latex/appendices/a-syntax-and-theories.tex) · [Independent report](INDEPENDENT.md)

## Proofs

* **Lemma A.7, p. 84.** The restriction idempotent $mr=\bar r$ fixes $f$. Leastness gives $\operatorname{ran}(f)\le mr$. Conversely, for every restriction idempotent $a$ fixing $f$, the regular image inclusion $m$ factors through the splitting of $a$. Thus $a(mr)=mr$, and choosing $a=\operatorname{ran}(f)$ gives the reverse inequality. The Lean proof already contains both inequalities and concludes by antisymmetry. [Range proof](../../../Lean/CategoricalEssentialIncompleteness/V46RegularImage.lean#L119)
* **Deletion and substitution.** At a head $z$, the equality pullback identifies $y=z$ on the true fiber of $\epsilon(y,z)$. For substitution of a variable for itself the capture test is true on the distinct-binder fiber because $\operatorname{mem}(y,[x])=\epsilon(y,x)=\mathbf f$ there. The equal-binder branch returns the original quantified formula directly. [Deletion step](../../../Lean/CategoricalEssentialIncompleteness/V46CategoricalDeletionLawsBoolean.lean#L110) · [Identity substitution](../../../Lean/CategoricalEssentialIncompleteness/V46CategoricalSubstitutionIdentity.lean#L139)
* **Propositional rules.** When $R_1=0$, uniqueness of the morphism out of $0$ gives $p_1=q_1$. The pullback projection $b_{1,q}$ supplies the required unary action on any carrier. This argument applies without assuming that $0$ is strict. [Unary closure](../../../Lean/CategoricalEssentialIncompleteness/V46PropositionalRuleClosure.lean#L58)

## Notation

| Passage | Notation in v89 |
|---|---|
| §A.1, change of base | Pullback along $!_P:P\to1$ is $!_P^*$. The natural isomorphism is displayed in the composite defining $\iota_P$. |
| §A.3, quantification | $X_{\forall}$ is the domain of the capture test $\chi_{\forall}$. The two maps to $\mathrm{Fm}\times E$ are $\forall\times1_E$ and the projection $\pi$. |
| §§A.4–A.6, rules and sentences | $B_n(Q,q)$, $p_n,q_n$ and the closure algebra $\alpha$ keep their mathematical roles. The sentence inclusion is $j$. Lemma A.7 denotes the splitting of $a$ by $i_a,s_a$. |

The paper retains all 77 numbered results and three numbered definitions in their previous order. All 161 labels resolve to the same numbers as in v88. The rebuilt PDF contains 102 pages. All 26 archive members equal the working sources byte for byte. The manuscript verifier and six axiom-parser tests passed. The Lean tree, verification scripts and dependency pins match v88. This edition has no new kernel receipt. [PDF](../../../manuscript/logical_consequence_and_essential_incompleteness_v89.pdf) · [Correspondence](../../../FORMALIZATION_STATUS_V89.md) · [Last full kernel receipt, v84](../../V84_WSL2_LEAN_VERIFICATION.md)

The endpoint formula cited in Proposition 10.1 remains equation (33) on p. 90. The v88 review followed its proof through p. 91 and checked equality of partial domains and values for both endpoints. [Endpoint review](../V88_REFEREE_AND_WRITING/ENDPOINT.md)
