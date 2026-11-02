# Comparison functors in the version 44 introduction

The word “source” in related work means the domain category of a range functor. The functor must be named before this use. Replace the historical phrase “beyond locally connected sources” by “beyond locally connected categories”; it otherwise invites an unintended identification with the paper's comparison functor.

## Exact types and roles

Theorem 3.1 uses a range functor `F : R → A`, where `R` is a recursion category with the stated ranges and coproducts and `A` is a restriction category with ranges, zeros and coproducts. Its logical application, Theorem 4.2, assumes `A` split and extends `F` to `Fhat : Split(R) → A`. The internally represented sentence theory is in `Split(R)`. Its interpreted theorem and refutation restriction idempotents belong to `A`.

Soundness supplies disjointness of these interpreted restriction idempotents. A total reduction from the pair defined using the Turing morphism, and a lift in `R` of the specified partial conditional in `A`, then give incompleteness both of the interpreted theory and of the represented theory in `Split(R)`. The theorem is not a transfer of inseparability from the target. In particular every disjoint pair of partial identities in `Pfn` has a separator, and neither target recursion nor target local connectedness is required.

| Application | Functor and categories | Locator |
| --- | --- | --- |
| Main arithmetic comparison | `F_M : S_PA → Pfn`, with `M = N` or an arithmetic ultrapower of `N`; extension `Fhat_M : Split(S_PA) → Pfn`; total part `G_M : B_PA → Set` | Section 6 definition and Proposition 6.1; Theorem 7.3 proof explicitly instantiates the logical comparison |
| Numerical argument | `J_rec : Rec → Pfn`, forgetting to sets and the same partial functions | Section 7.5, beginning |
| Miller argument | `I_p J_p : E_a → K_p`, with `K_p = Split(Rec^p)` and `p` a binary representation of `a` | Section 8, preceding inseparability construction |
| Cosheaf argument | Full inclusion `I : R_X → Par(E,Mono)`, with `E` the regular category of computable forks constructed there | Section 9, full inclusion immediately before the source-conditional corollary |
| Auxiliary faithful family | `F_T : S_T → D_T = product_{M in M_T} Pfn`, where `M_T` consists of all models of `T` carried by `N` | Appendix D, opening definition and Theorem D.1 |

`Pfn` is the category of sets and arbitrary partial functions. A model used for interpreting codes is distinct from the model of the represented axiom theory used for truth of decoded formulas. The main arithmetic application fixes the computational equality theory `PA`; it varies the represented axiom theory.

## Suggested local wording

The comparison theorem uses a range functor $F:\mathscr R\to\mathcal A$, with source recursion category $\mathscr R$ and target restriction category $\mathcal A$. For its application to internal theories, $\mathcal A$ is split and $F$ extends to $\widehat F:\Split(\mathscr R)\to\mathcal A$. Soundness supplies disjointness of the interpreted theorem and refutation restriction idempotents in $\mathcal A$. Under the reduction and lifting hypotheses of Theorem~\ref{thm:logical-comparison}, the Turing morphism in $\mathscr R$ then yields incompleteness of the represented sentence theory in $\Split(\mathscr R)$ and of its interpretation in $\mathcal A$.

For arithmetic, the functors are $F_M:S_{\PA}\to\Pfn$, where $M$ is standard arithmetic or an arithmetic ultrapower of it, and $\Pfn$ denotes sets and partial functions. Appendix~\ref{sec:family} instead combines model interpretations into a functor from $S_T$ to a product of copies of $\Pfn$. The Miller and cosheaf applications use the split category of partial functions recursive relative to one binary representation and a partial-map category of computable cosheaves, respectively.

The last sentence is optional if its terminology would require an overlong catalogue in related work. The exact targets can instead be named where those applications are previewed. Do not merge all three applications into the semantic-consistency route: the Miller and cosheaf arguments use the source-conditional inseparability corollary before applying the theory-extension criterion.

Scope: current comparison statements, their logical application, concrete arithmetic instantiation, and the displayed auxiliary/application functors. No manuscript files edited; no new whole-paper proof audit.
