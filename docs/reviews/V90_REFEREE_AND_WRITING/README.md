# Appendix B referee and writing review

The review covers the ten numbered results B.1–B.10, the intervening arguments and the use of (33) in Proposition 10.1. The first reader reconstructed Appendix B from v89 before comparing it with the Lean declarations. A separate reader reconstructed the dominance, frame and evaluator proofs, including both inclusions between the domains in B.7. Both read the revised text. [Reviewed manuscript](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/bcf251f293cdc8202a1130f2962005f6486275fd/manuscript/latex/appendices/b-three-point-cosheaves.tex) · [Independent report](INDEPENDENT.md) · [Evaluator review](EVALUATOR.md)

## A. Mathematical blockers

None found in the reviewed arguments. The fork restriction equivalence preserves the distinction between a restriction idempotent, which splits through its domain, and an arbitrary idempotent, which splits through its image. For the latter, $p^2=p$ puts each $p_j(D_j)$ inside $D_j$ and forces $p_j$ to fix it pointwise. [B.8–B.9 in the independent report](INDEPENDENT.md)

## B. Major weaknesses

None found in Appendix B. In Theorem B.7, the domain of the center evaluation requires all three computations to halt and their values to satisfy both transition equations. For a parameter representing $F$, membership in the domain of $F_0$ gives halting of the endpoint computations and naturality gives their values. Conversely, halting at the center requires halting of the specialized center program, whose domain is precisely that of $F_0$. [Evaluator review](EVALUATOR.md)

## C. Notation and exposition

| Passage | Reading in v90 |
|---|---|
| B.1, proper nonempty opens | $O_0=\{c\}$, $O_1=\{a,c\}$ and $O_2=\{b,c\}$ follow the vertex order of §10. $D_f$ denotes a domain subfunctor. Appendix A retains $L$ for the logical axioms. |
| B.1, pushout | The diagram has components $Y_j$ and transitions $r_i^Y$. A diagram morphism $f:Y\to Z$ induces the map on pushouts determined by $f_X\iota_i^Y=\iota_i^Z f_i$. |
| B.3, weak choice | The partial inverse on the image is $p^\dagger$. The specialization functions in B.7 are $s_j$. |
| B.7, evaluator | Each candidate computation is a partial function $\psi_j:V_0\times V_0\rightharpoonup V_j$. The comparison $\psi_i=r_i^V\psi_0$ is imposed on the center domain. $Q$ is the Karoubi equivalence in B.9 and §10. |
| B.7–B.9, arity and inclusions | The component arity is $m(Y_j)$. The domain and image inclusions use $\iota$. The dominance embedding is $s_Z$ as in Lemma B.5. |

## D. Agreement with §10

Equation (33) retains the program in the second parameter coordinate and gives the same partial value at each endpoint. The equation and the specialization display are byte-identical to v89. The compatibility equation changes only in the names of its computations. The 15 Appendix B labels retain their order. [Endpoint and center graph checks](../../../Lean/CategoricalEssentialIncompleteness/V46ForkTupleTuringChecks.lean#L63)

## E. Verification

The rebuilt paper has 102 pages. All 161 labels retain their numbers, and all 26 archive members agree byte for byte with the working sources. The manuscript verifier and the six axiom-parser tests passed. [Paper](../../../manuscript/logical_consequence_and_essential_incompleteness_v90.pdf) · [Correspondence](../../../FORMALIZATION_STATUS_V90.md)

## F. Scope

These readings found no mathematical error or open Lean obligation in Appendix B. The Lean tree, verifier and dependency pins match v89. The current check compared manuscript statements with proof sources and rebuilt the paper. The last full kernel replay tested v84. [Kernel report](../../V84_WSL2_LEAN_VERIFICATION.md)
