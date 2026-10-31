# Independent review of Version 8, Sections 1–4

Reviewed `tmp/v8_sections1_4.tex` continuously from the preamble through the end of Section 4 (905 lines), including the abstract and introduction. I compared the changes with Version 7. I did not write or edit this fragment.

No material mathematical error was found in this bounded review. Two short type declarations should be made explicit. Neither requires an additional proof or an expansion of an elementary argument.

## Concrete repairs

| Anchor | Finding and severity | Exact repair |
| --- | --- | --- |
| Section 4.2, line 783, “one oracle computation $\Psi$” | The input/output types and totality follow from the displayed approximation, but the new numerical function family is not explicitly typed. This is a minor exposition issue under the author's explicit-type requirement. | Replace the lead-in by: “The preceding construction gives a single oracle program whose numerical functions $\Psi^p:\N^2\to\N$, for $p\in2^{\N}$, satisfy”. Keep the approximation display and subsequent parameterization equation. |
| Section 4.3, line 833, “For $E\subseteq Y$” | The defining equation uses $1_E$ as an arrow of $\mathcal E_a$. The target subset should therefore be explicitly included in the class just declared. This is a minor scope/typing clarification, not a failure of the splitting construction. | Write: “For another $\mathcal E_a$-semidecidable subset $E\subseteq Y$, a morphism $D\rightharpoonup E$ is represented by …”. |

The formerly ambiguous summand-proof phrase is already repaired: the source now says “the equality involving $a$” and “the equality involving $b$”. No further change is needed there.

## Outline, flow, and mathematical boundaries checked

| Portion | Function and check |
| --- | --- |
| Abstract and introduction | State the lifting criterion and the Miller, syntactic, arithmetic, and cosheaf applications. The lifting condition remains an assumption; the preview does not claim that faithfulness alone supplies it. The inverse-image operation is assigned to the total sentence map. The syntactic arrows are described as classes of typed indices. |
| Related work | Distinguish existence of a recursion structure from inseparability in a source already having one. The revised phrase about PA-provable equality does not identify standard equality with provability. No new external attribution was independently verified in this pass. |
| Section 2 | Define restrictions, total arrows, splitting, products, coproducts, range functors, local connectedness, and Turing morphisms. The ordinary partial-function examples are explicitly introduced as concrete interpretations. The splitting identity and the condition for a split arrow to be total are both stated. |
| Section 3.1 | Construct the target switch and prove the main criterion. The new equations with $\varepsilon_i$ remain equations between abstract arrows. The two separator inequalities are correctly directed. The final contradiction uses totality and preservation of joins in the target; it does not assume preservation of source products by $F$. |
| Sections 3.2–3.3 | Prove the disjoint-join sufficient condition and the inverse-image incompleteness corollary. The revised application paragraph assigns consistency and completeness to the specified logical representations. The following paragraph distinguishes preservation of a pair under splitting from the separate construction of syntax. |
| Section 4.1 | Define binary names and exact-domain oracle computations, construct the unanimity morphism, and verify the category and interpretation functors. The search terminates exactly when a common output exists on the whole compact name set. Range and inverse searches return name-independent results; the parameterization equation includes simultaneous undefinedness. |
| Section 4.2 | Construct the strict-cut reduction and prove the separator comparison. The box-distance functions and series tail bounds yield the uniform total approximation. Parameterization fixes $e$ without introducing oracle-dependent indices. The argument that $J_p\tau_a$ is not Turing now specifies $I_p$ and its switches. Its diagonal pair is separated by $h^{-1}(C_p)$, as required. |
| Section 4.3 | Declare the concrete splitting presentation, construct the real-closed-field theory and proof domain, and apply the corollary. The equations $f=1_Ef1_D$ and $\bar f=1_D$ distinguish an arrow of the splitting from a total arrow. Restriction of code operations to their carriers preserves exact domains. The theorem/refutation inclusions and consistency equation have the stated types. |

The paragraph functions remain mathematical: definitions, constructions, theorem statements, proofs, comparisons, and application explanations. The cuts and added equations preserve the reading order. I found no new editorial-process prose, reassurance-only paragraph, or passage requiring a broader rewrite. The direct presentation by typed maps and equations is consistent with the requested use of Heller as an expository model.

## Preservation and scope

All ten theorem, proposition, lemma, and corollary statements in the fragment are identical to their Version 7 counterparts after whitespace normalization. No existing label was removed. The only added label is `def:miller-splitting`, which supplies the reference required by the new Appendix B.4. The exact-domain requirements in the Miller category, unanimity lemma, and proof-conclusion construction are retained.

A separate narrow check of the new uniform approximation, hypothetical Turing argument, splitting declaration, and real-closed-field proof also found no new material type or domain error. Its assessment is supplementary; the full fragment was read independently here.

This review checks the exposition, the changed inferences, and the explicit boundaries in this fragment. It is not a new verification of the Miller or Bauer–Hanson source theorems, all bibliographic claims, or the later sections. I did not compile, render, edit, formalize in Lean, commit, or push the manuscript. No further elementary proof expansion is recommended.
