# Version 46 final mathematical-writing review

Reviewed the exact frozen source of *Logical consequence and essential incompleteness in recursion categories*, Version 46, 2 November 2026, in `tmp/revision46/frozen`. I read the complete manuscript continuously in `main.tex` order, including all four arithmetic input files, appendices, bibliography, and source comments, then read the complete v45–v46 diff and the five editing logs. No manuscript file was changed.

The cuts preserve the reader's path and the essential mathematical distinctions. I found no broken referent, overcompressed proof, unsupported use of “raw,” or remaining duplicate argument requiring consolidation. One repeated background definition in Appendix B can still be reduced. Appendix A's overlap with Section 2 is required by the author's independent-scope constraint and is not a finding.

## Governing source and actual outline

Read c20 `revise-mathematical-prose` and both supplements, and the supplied `tmp/review_sources/klr.txt`, §1 and §§4–5. Verified relevant advice: self-contained theorem statements (§1.5), connected exposition and complementary explanations (§1.10–13), important displays (§1.16), readable sentences (§1.17), and contextual definition placement (§§4–5). The inline default and the removal of repeated material are the user's instructions; they are not attributed to an invented KLR prohibition of displays or all repetition.

| Existing portion, in order | Mathematical function |
| --- | --- |
| Abstract and Introduction, including Related work | State DPH's problem, the two criteria, the three applications, and their antecedents and distinctions. |
| Categorical preliminaries | Define restriction structure, ranges, splittings, products/coproducts, connectedness, and recursion/Turing categories. |
| Diagonal comparison and complementary conditionals | Prove comparison, lifted separators, source inseparability, and the disjoint-join sufficient condition. |
| Internal theories and semantic consistency | Construct and interpret sentence theories; derive the semantic and source criteria. |
| Syntactic recursion category, total splitting, syntax/lists, substitution, derivations/theories | Realize the categorical hypotheses with provable graph equality and parameterized initiality. |
| Interpretation and soundness | Interpret models, lift complementary source conditionals, prove standard-code soundness, and transfer it to ultrapowers. |
| Arithmetic application, indexed theories, uniform independent sentences, numerical realization/incompleteness, numeral instances | Apply the two criteria, establish the family/fiber comparison, and distinguish the numerical realization from provable totality. |
| Miller application | Build the representation-independent category, reduce the cut pair, prove its separate realization, and apply it to the field theory. |
| Three-point application | Construct component theories, retain naturality/initiality, and prove endpoint essential incompleteness. |
| Appendices A–D | Give independent categorical syntax/theory foundations; prove the cosheaf structure; exhibit missing lifts; establish faithful model families and theory extension. |

No revised outline is warranted.

## Remaining actions

| Frozen-source anchor | Actual issue | Basis and concrete repair |
| --- | --- | --- |
| `appendices/b-three-point-cosheaves.tex:60–64` | The definitions of regular epimorphism, regular category, and regular image repeat A.1. Appendix B has no independent-scope requirement. | User's consolidation instruction; this is duplicate background, not KLR's complementary explanation. Replace the text from “A \emph{regular epimorphism}” through “its \emph{regular image}.” by `Use the regular-category terminology of Appendix~\ref{app:categorical-hypotheses}.` Retain the ensuing kernel-pair, slice-category, and extensivity definitions, including the displayed slice equivalence. |
| `sections/05a-internal-syntax.tex:613` and `appendices/c-section-lifting.tex:78` | Two dispensable instances of “usual” remain. | Local adjective deletion under the user's economy instruction: “the substitution equation” and “their universal properties.” These are polish, not mathematical defects. |

## Preserved dependencies and notation

Restriction/splitting/range notation is defined in Section 2 and independently where Appendix A needs it. The new named-variable syntax convention remains explicit; the contrast with syntax modulo renaming survives. Functional search precedes its applications. The arithmetic code model and the structure satisfying the decoded axioms remain distinct. Arbitrary parameter objects, explicit sources/targets, proof-record versus value uniqueness, the partial/total distinction, the single-program condition across all Miller representations, and component naturality in the three-point realization all remain visible.

The DPH/Löb methodological account, Ramesh's separate introspective-theory account, source credits at construction openings, and the categorical versus pointwise cosheaf distinctions remain. The numerical, syntactic, Miller, and functor-category initiality arguments establish different universal properties and should remain separate. The specialized `[C]_T` witness search precedes the predicate-category lemma and is not safely removed by a forward reference. The three ultrapower representative adjustments have different immediate conclusions and remain brief at their points of use.

The remaining displays are numbered/referenced identities, substantive constructions, multi-equation comparisons, case definitions, or diagrams. I found no further source-level display change necessary. Rendered line breaks and page layout were not assessed in this subtask; the parent owns the exact-source build and rendering check. Literature claims were preserved rather than independently reverified. This is an editorial/dependency review, not a correctness or novelty certification.

## Resolution check

Verified the three applied local changes in both `output/manuscript/local_connectedness` and `tmp/revision46/frozen`; the corresponding files are byte-identical between those trees. Appendix B now says “We use regularity and regular images as in Appendix~\ref{app:categorical-hypotheses}.” The target label and A.1's definition remain, and the following kernel-pair, slice-category, and extensivity definitions, including the slice-equivalence display, remain intact. Appendix A's independent restriction/splitting/range/functor definitions are retained. The two “usual” instances are removed with their surrounding assertions unchanged. All findings in this report are resolved; no new broad review or rendering claim is made by this resolution check.
