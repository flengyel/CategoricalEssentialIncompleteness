# Review of the revised paper and separate note

The local findings are corrected, and the second hostile-referee and mathematical-writing checks found no remaining required correction in the changed passages. No mathematical blocker was confirmed in the revised arguments.

## Scope

The paper review covered the version 28 revision in its full mathematical context: the conditional criterion, model and numerical applications, Miller and cosheaf applications, Appendices C and D, and the corresponding abstract and introduction changes. It did not repeat an audit of the unchanged proofs throughout the 77-page paper. The complete 13-page note was read, and all 18 numbered claims were traced. A separate agent checked the outline, dependencies and types.

The mathematical-writing reviewers consulted Knuth, Larrabee and Roberts, *Mathematical Writing*, Section 1 and Sections 4–5. Their source-based recommendations are distinguished from explicit-typing and terminology preferences in the detailed reports.

## Corrections in paper version 29

| Passage | Finding | Correction |
|---|---|---|
| Introduction | The categorical conclusion was called recursive inseparability, although the definition concerns restriction idempotents. | State “inseparability of restriction idempotents”. Numerical recursive inseparability remains in the applications. |
| Introduction and Section 3 | “Exchange the coproduct tags” gave an informal description of morphisms on an arbitrary categorical object. | Say that the morphisms agree with opposite coproduct injections on complementary source domains; retain both defining equations. |
| Introduction roadmap | The section range included Appendix D, and the incompleteness corollary was assigned to the wrong section. | Follow the actual section order and identify the appendices separately. |
| Appendix C, Proposition C.1 | “The specified pair” was not specified within the statement. | Quantify the Turing morphism and coproduct isomorphism and display the two restriction idempotents. |
| Appendix C proof | The proof still verified target properties used by the relocated criterion. | Retain the hypotheses of the current comparison theorem and the concrete counterexample; remove the unused splitness, local-connectedness and weak-choice verification. |
| Appendix D, Corollary D.2 | A source conditional hypothesis was attributed to the interpretation functor. | Give the total source morphism and its two equations, then verify the functor and target hypotheses separately. |
| Cosheaf endpoint application | “Switching sections” retained an unexplained name from the previous formulation. | State the type and equations of the conditional, referring to the existing numerical construction without repeating its proof. |

The comparison proof, the representation-independent Miller search, and the natural inverse of the cosheaf copairing retain their explanatory steps. No theorem hypothesis, application or local-connectedness result was removed. The standalone Appendix A has matching version 29 exports; its mathematical text is unchanged.

## Corrections in note version 2

The range and partial-monomorphism definitions now quantify the common sources and targets of their test morphisms. The domain operations have the signatures

\[
f^*:\mathrm{Dom}(Y)\longrightarrow\mathrm{Dom}(X),\qquad
f_*:\mathrm{Dom}(X)\longrightarrow\mathrm{Dom}(Y).
\]

Proposition 2.1 now states the types of the Turing morphism, the indexed morphism, and the external function

\[
N:\mathbf C_T(Y,Y)\longrightarrow\mathbf C_T(Y,Y).
\]

Its proof replaces “duplicate the resulting parameter map” by a total morphism \(c:V\to X\), the total morphism \(g=\Delta_Xc:V\to Y\), and the equation

\[
t(g\times1_Y)=a^{-1}\tau(c\times a)=f.
\]

The two uses of “range agreement” now name the defining equality property of the relevant range. Two adjacent announcement or repetition sentences were removed, a comma splice was corrected, and “surrogate for points” was replaced by the attribution. The theorem environments share one counter within each section, replacing numbers such as 4.0.4 with ordinary section-based numbers. All 18 claims, their hypotheses and their dependencies remain. The bibliography, acknowledgments and preserved `LOCOct10f` files are unchanged.

## Verification and limits

The paper has 77 pages, the note 13, and the standalone appendix 10. All three final LaTeX logs have no undefined references, undefined citations, overfull boxes or warnings. The source archive contains 23 entries matching the current source bytes.

The rendered paper pages 1, 2, 6, 52, 72 and 75, note pages 1 and 4–10, and the standalone appendix's first page were inspected visually. No layout correction was needed.

The reviews did not reverify external literature claims against all primary mathematical sources, certify novelty, or run Lean. The second review checked the corrections and their mathematical dependencies; it did not restart a whole-paper audit.

Detailed records are in the paper repository's [version 29 review directory](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/main/Audit/2026-11-01-prose-types-v29) and the note repository's [version 2 review directory](https://github.com/flengyel/notes/tree/main/recursion_categories/reviews/ranges_and_inseparability_v2).
