# Focused dependency and Mathematical Writing review — uniform family

Scope: the proposed version-22 subsection “An indexed family of arithmetic theories” in `tmp/uniform22/uniform_draft.tex`, read against Appendix A’s rule and theory construction, the syntactic derivation realization in §5, and the arithmetic comparison in §7.1. The governing writing source was Knuth–Larrabee–Roberts, *Mathematical Writing*, §1, consulted in `tmp/review_sources/klr.txt`. This is a focused source review, not a review of the entire manuscript or a novelty assessment.

The new subsection uses the appendix’s results without repeating their proofs. Its additional categorical argument is the decomposition of the inference endofunctor at a complemented numeral point. The original numerical insertion/erasure argument has been replaced by that shorter argument; no new tree coding or fold proof is needed.

## Actual outline and dependencies

1. **Presentations and their common parameter object.** Define `B=B_PA`, the inclusion into the restriction splitting, `E=I(ω)`, the external sentence presentations Γ_e, and the internal axiom subobject `A↪E×S`. Literal specialization of the common predicate fixes the internal object associated with each presentation.
2. **Family rule morphisms.** Reuse the logical axioms and rules from Appendix A, adjoining the same E-coordinate to each premise and conclusion. Apply the existing syntactic initiality lemma to these new rule data on `E×Fm`.
3. **Family theorem subobject.** Restrict conclusions to sentences and take the regular image. Apply Appendix A’s least-closed-image theorem and range/image lemma.
4. **Fibers of the derivation family.** Split the parameter object into the numeral point and its complement. Finite extensivity decomposes the slice category; the common parameter makes the inference endofunctor and its algebra category decompose. Initiality then passes to the particular numeral component. Regular-image stability gives the theorem fiber.
5. **Uniform independent sentences.** Use one Σ1 conclusion-image predicate and one partial proof-search map with paired input. The parameterized Turing property gives a total source parameter map. The already proved soundness and diagonal-domain lemmas show independence for each consistent standard presentation.

## Reuse of existing arguments

| Existing result | Use in the new subsection | Treatment |
|---|---|---|
| `lem:syntactic-total-category` | Predicate presentation, regularity, finite extensivity, partial inverses for monomorphisms | Cited; its construction is not repeated. |
| Appendix A’s logical axiom and inference-rule morphisms | Define the family rules by products with E and the new axiom subobject | Reused by name; the seven schemes, binding syntax, side conditions and substitution proofs are not recopied. |
| `lem:syntactic-derivation-initiality` | Existence of the family’s initial derivation algebra on `E×Fm` | Cited; no finite-tree coding, evaluation algorithm, induction or uniqueness proof is repeated. |
| `thm:least-theorem-subobject` | Identify the image of the full family conclusion map | Cited; the epi–mono argument and leastness proof are not repeated. |
| Regular-image pullback stability and `lem:range-regular-image` | Sentence restriction, numeral theorem fibers, and the family range | Applied to the newly typed maps; no general proof is repeated. |
| `lem:syntactic-functional-search` and `lem:arithmetic-proof-search` | Uniform partial search on paired input `(e,x)` | Cited; no repeated bounded-search correctness proof. |
| `prop:standard-code-soundness` and `lem:arithmetic-diagonal-representation` | Disjoint proof/refutation predicates and the final contradiction | Cited; no semantic substitution, logical soundness, or finite-trace-to-proof argument is repeated. |

## Writing and typing findings

The following applications of KLR §1 were checked: point 5 on theorem scope, points 10–13 on connected explanation and defined variables, and points 14–15 on consistent notation and economy. The exact category-typing requirements and the user’s prohibition on repeating Appendix A are additional project requirements, not quotations from KLR.

| Anchor | Issue | Action and status |
|---|---|---|
| Definition of `i:A↪E×S` | The initial wording placed the B-object `E×S` “in the predicate presentation.” | Changed to say that the predicate represents a subobject **in B**, through the predicate presentation. Resolved. |
| Definition of the family theorem image | “Its sentence pullback” had an avoidable ambiguous antecedent. | Changed to identify the pullback of the full conclusion image explicitly along `1_E×j`. Resolved. |
| Identification with the range | The range/image lemma has a partial-inverse hypothesis. | The draft now explicitly invokes `lem:syntactic-total-category` for the partial inverse of the image mono before invoking the range/image lemma. Resolved. |
| Fiber proposition’s upper arrow | The original name `ins_e` referred to a numerical algorithm removed from the proof. | Renamed to `ι_e`, the induced algebra comparison. Resolved. |
| Fiber proposition proof | Pullback preservation of arbitrary initial algebras would be unjustified. | The new proof explicitly identifies the inference endofunctor componentwise, including the nullary summand and naturality on morphisms, and proves component initiality using the product of algebra categories. This is the needed new argument. |
| Uniform theorem | A total arrow assigning sentences must be distinguished from the partial proof-search arrow and from an external numerical function. | The draft types `ℓ` and `g` in `S_PA`, then types `q=θI(g):E→S` in B. Its conclusion is stated only for consistent standard fibers. No repair needed. |

The categorical numeral decomposition preserves the proof’s substantive dependency: the common E-coordinate in the premises and conclusion is what makes the inference endofunctor decompose. The draft states this and verifies the pullback-defined rule summands, rather than citing extensivity as if it automatically preserved initial algebras.

The definitions of E and Γ_e make clear that E indexes axiom presentations. The text does not identify those indices with distinct deductively closed theories. It does not introduce an internal consistency decision or infer source consistency by reflecting target zero. No invented terminology or editorial/process commentary was found in the reviewed mathematical insertion.

No further source edit is required by this focused review. Appendix A should remain unchanged. The parent agent is responsible for integration, cross-reference checking, compilation and visual inspection of the final version; those checks were not performed by this reviewer.
