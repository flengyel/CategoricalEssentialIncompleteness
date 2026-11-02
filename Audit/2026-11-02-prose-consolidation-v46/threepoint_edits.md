# Version 46: three-point application prose pass

Scope: `sections/09-three-point-space.tex` and `appendices/b-three-point-cosheaves.tex` in *Logical consequence and essential incompleteness in recursion categories*, Version 46, 2 November 2026. Both files were read completely before editing and read continuously after editing. The supplied `tmp/review_sources/klr.txt` was consulted at §1 (especially points 5, 10–17, 23, 26) and §§4–5. The inline preference is the user's instruction; KLR §1.16 supports retaining important displays.

## Existing outline and dependencies

- §9 opening: cosheaf and fork construction, numerical carriers, partial maps, universal object, and recursion-category summary.
- §9.1: total conditional from complementary subfunctors, with computable inverse components and naturality; inseparability by `cor:source-conditionals`.
- §9.2: component evaluation, preservation and endpoint universality, probe functors, and failure of universality at component 0.
- §9.3: inseparable atomic labels; formula and derivation objects with initiality; least theorem subobject, consistency, component inseparability, and essential incompleteness.
- Appendix B.1: cosheaf equivalence, quotient and product/subobject distinctions, regularity and extensivity.
- Appendix B.2: partial-map structure, range laws, weak choice, and local connectedness.
- Appendix B.3: universal embedding and nonempty-word frame (not the syntax list object).
- Appendix B.4: component computations and naturality for a Turing morphism.
- Appendix B.5: recursion-category structure, restriction/Karoubi splittings, and distinction from `Rec`.

## Implemented repairs

| Anchor | Difficulty and action | Basis |
| --- | --- | --- |
| §9.1 after `cor:source-conditionals` | Replaced repeated five-versus-two-subobjects argument by the unchanged self-contained non-equivalence claim and citation `prop:fork-distinction`. Appendix B retains the full proof. The cited proposition has exactly the same `R_X` versus partial-recursive-functions conclusion and uses the same `E=C_rec^J` and `C_rec`. | User-authorized consolidation; KLR §1.10–13 connected exposition and reader economy. |
| `prop:endpoint` proof | Replaced the repeated endpoint computation by `eq:fork-turing-endpoint`. That equation describes the same `E_i(tau)=tau_i`, `i=1,2`, with the same encodings and acceptable numbering. The parameter-map argument remains. | Precise reuse of an existing formula; no new reference. |
| Short unnumbered definitions/equalities in §9 and Appendix B | Moved short formulas inline, including the definition of `A`, copairing `q`, conditional `ell_c`, atomic pullbacks, constructor morphism types, the pair assignment, concatenation/singleton morphism types, the universal-property equation, and parameter/naturality computations. | User's inline default; numbered/referenced and longer explanatory displays retained. |
| `lem:fork-dominance` proof | Removed the immediate repetition of the lemma's fixed object hypothesis. | Economy without loss of a premise. |
| Probe paragraph and partial-map/specialization prose | Removed duplicated “defines … defining” and dispensable “just,” “precisely,” and “usual.” | KLR §1.7, 17, 26. |

## Paragraph function audit

Blank-line blocks are numbered in final source order, with headings counted separately. Blocks containing a statement immediately followed by its proof receive both roles. Every prose block was assigned a mathematical function; none was solely an editorial reassurance.

- §9: headings 1, 11, 13, 19; problem/contribution 2; definitions/constructions 3–8, 14, 17, 20, 23, 26–30, 33, 36; structural results/dependencies 9–10, 22; proof/construction and cited distinction 12; statement/proof 15, 24, 31, 34, 37, 40; proof continuations 16, 21, 25, 32, 35, 38–39; counterexample 18.
- Appendix B: headings 1–2, 12, 20, 28, 38; definitions/constructions 3, 5, 7, 21, 23–24, 29–30, 44–45; counterexamples/distinctions 6; statement/proof 4, 8, 13, 18, 22, 25, 39, 42, 46; theorem statement 31; proof continuations 9–11, 14–17, 19, 26–27, 32–37, 40–41, 43, 47.

## Definition/type and deferred-candidate checks

- Retained the explicit ambient-power/carrier convention, the subfunctor component maps, the typed Turing parameter maps, and all theorem hypotheses.
- Retained `q_j^{-1}` computability and naturality in §9.1: numerical membership search alone does not prove the required natural transformation.
- Retained both formula/proof initiality arguments and their naturality inductions; numerical tree evaluation alone does not establish an initial algebra in the functor category.
- Retained Appendix B's nonempty-word frame and component inverses: this construction differs from Appendix A's syntax list object.
- Retained the component-0 counterexample and the product/subobject counterexamples; these establish substantive failures rather than defensive disclaimers.
- Retained all numbered equations, labels, and all substantive proof steps. No further consolidation was judged safe or useful in this scope.

Checks: balanced LaTeX environments and display delimiters in both files; all 36 §9 and 15 Appendix B `ref`/`eqref` targets resolve in the current manuscript. No process commentary was inserted into manuscript source. No compilation or rendered-page inspection was performed by this subtask; the parent owns integrated verification.
