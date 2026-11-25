# Appendix E referee and writing review

Appendix E has seven subsections. They follow seven proofs, from the free first-order adjunction in E.1 to the Miller theorem domain in E.7. The edition at `7169791` is v90. Its Appendix E was byte-identical to v89 and v91. The revising readers compared all seven passages with the mathematical arguments and the pinned Lean sources. [Revised appendix](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/54af305c983dad846deea35c5b3385c853fa3d2a/manuscript/latex/appendices/e-reading-lean-proofs.tex) · [Mathematical reading](INDEPENDENT.md) · [All twenty source links](LINKS.md)

## A. Mathematical blockers

No open proof obligation arose in the seven arguments. The outstanding inference reported for Lemma A.7 was published in v89. The restriction idempotent $mr=\bar r$ fixes $f$, so the definition of range gives $\operatorname{ran}(f)\le mr$. Factoring the image inclusion through every fixing idempotent and then taking that idempotent to be the range proves $mr\le\operatorname{ran}(f)$. [Manuscript fix at its original commit](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/31c64416f69720e520febd3d4153eb4fce2b0403/manuscript/latex/appendices/a-syntax-and-theories.tex#L551) · [Lean proof](../../../Lean/CategoricalEssentialIncompleteness/V46RegularImage.lean#L119)

## B. Major weaknesses

None found in the audited passages. In E.4 the conditional exchanges the summand domains. After pullback along $Fg$ the two domains become equal and remain disjoint, so both are zero. In E.6 a proof of the even-output sentence selects the odd branch, which yields its refutation in PA. The reverse branch excludes a refutation in the same way. [Mathematical reading](INDEPENDENT.md)

## C. Notation and link ranges

| Passage | Notation in v92 |
|---|---|
| E.1–E.2 | The pair and theory are written $(X,a,b)$ and $(P,T)$. The two subobject carriers in E.2 are $X_a$ and $X_b$. |
| E.4–E.6 | E.4 uses $Fg$ directly. In E.5, $\operatorname{ev}$ is evaluation at the theorem point, $B$ takes constant families on total morphisms, and $\varepsilon:\operatorname{ev}B\cong1$ is the projection. E.6 retains the number object $E$ and the program index $e$ used in §8. |
| E.7 | $A$ is the family of axioms over the parameter object. The unique interpretation in the algebra $\beta$ is $\widehat\beta:D_A\to Q$. An arbitrary axiom mono has source $Z$. |

The two E.7 links now select all of `theorem_mem` and `sentence_image_recovery`, through lines 98 and 192 of their respective files. The other eighteen ranges already included their concluding declarations. [Link inventory](LINKS.md)

## D. Agreement with the sources

Di Paola and Montagna’s PR-extension convention (p. 644), definition of the unprimed syntactic category (p. 646), and non-local-connectedness result (pp. 657–658) agree with the passages that cite them. In the sound case of Corollary 4.4, a fixed $[e]_T\ne1_T$ agrees with the identity after precomposition with every connected $[c]_T$. The zero-product law used for prodominicality in the manuscript is the authors’ condition $(*)$ on p. 645. [Facsimile comparison](CITATIONS.md)

## E. Verification

All twenty different Lean hyperlinks in the compiled PDF, on pp. 97–100, match the twenty LaTeX source references. The fourteen target files match tag `cei-v72-palomar-v3` byte for byte. The document has 102 pages. All 161 labels retain their numbers, and all 26 archive members match the working sources. The manuscript verifier and six axiom-parser tests passed. [Paper](../../../manuscript/logical_consequence_and_essential_incompleteness_v92.pdf) · [Formalization correspondence](../../../FORMALIZATION_STATUS_V92.md)

## F. Scope

This report covers Appendix E, the reported Appendix A inference and the specified Di Paola–Montagna citations. The section-by-section review identified no remaining mathematical proof obligation. The Lean tree, verification scripts and dependency pins agree with v91. The last full kernel replay tested v84. [Kernel replay](../../V84_WSL2_LEAN_VERIFICATION.md) · [Current WSL2 handoff](../../CODEX_WSL2_CEI_V92_LEAN_HANDOFF.md)
