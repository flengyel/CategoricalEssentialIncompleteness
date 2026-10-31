# Independent review of version 8, Section 9 and Appendix A

Reviewed the complete initial fragment `tmp/v8_sections9_A.tex` (1,016 lines), including all statements, proofs, diagrams, and comparison constructions. This is an independent reading of another agent's revision. Section 8's definitions of `Rec`, its carrier functor `J`, and `Pair(Rec)` were consulted to check the references across sections. A dependent follow-up checked the final numerical-conjugation correction in the 1,024-line fragment against the carrier bijections defined in Section 5. No manuscript edits were made by this reviewer.

The governing standard is explicit mathematical typing and justified comparison between presentations. Heller's exposition is the requested model. The author's latest instruction permits citation of elementary standard arguments and requires all types to remain explicit, particularly for subsequent formalization. This review does not request duplicate proofs of standard recursion-theoretic facts.

## A. Hard blockers

No counterexample or new construction gap was found in this portion. This is a bounded finding about the reviewed text, not a certification of the whole manuscript or its formalization.

## B. Mathematical checks

- **The numerical comparison.** The initial review missed a carrier mismatch, subsequently identified by the other reviewer: the raw carrier `J(X)=|X|` need not literally be a subset of a finite power of `N`. The final version first forms the numerical conjugate `hat f = γ_Y ∘ J(f) ∘ γ_X⁻¹ : N ⇀ N`. It then defines `Q_num(X,e)` as the c.e. subset `D_e⊂N` on which `hat e` is the identity and sends an arrow to `hat f` restricted to the indicated domains. The inverse hom-set assignment extends by undefinedness and conjugates back. The displayed carrier bijections cancel in composites, take identities to identities, and preserve restriction domains. Essential surjectivity is expressed by an isomorphism in `K`; `γ_ω=1_N` makes the displayed object `Q_num(ω,e_k)` exactly `k(C)`. This dependent check verifies the correction rather than retaining the initial review's overly favorable statement.
- **The source of endpoint inseparability.** The full subcategory `K_2` generated from `N²` by the chosen binary restriction products and coproducts is named. Its objects are recursively isomorphic, and fullness retains the Turing morphism and total parameter maps. Restrictions and ranges are endomorphisms of retained objects. The carrier functor, complementary-domain sections, and parity isomorphism are specified before the lifting theorem is applied.
- **The proof-object preview.** The polynomial functor is defined on objects and morphisms. The formula algebra has its structure map and equation. The slice object `(Prf,c)` is separately equipped with the structure map `δ` of an initial `H`-algebra. The two atomic inequalities are credited to leaves; the zero-intersection equation is credited to the consistency proof.
- **The fork Turing morphism.** Each component is a numerical partial recursive function with a specified domain. The two endpoint domains contain the images of the central domain, and the central output tests establish naturality. For an arbitrary partial arrow, the membership guard makes each specialized numerical function have exactly the given component domain. The assembled parameter map is total and natural. The concluding equation checks both values and domains.
- **Loss of universality at component 0.** The argument uses the naturality equation on the specified domain subfunctor. Varying the central coordinate while fixing its endpoint image gives the stated contradiction. It does not substitute standard program indices for arbitrary categorical parameters.
- **Partial-map and total-category constructions.** Finite limits, images, coproducts, partial-map composition, restriction domains, range agreement, weak choice, connected restrictions, the frame, and the splitting comparison were checked in their declared concrete categories. Element arguments here are confined to the explicitly numerical carriers. The two-subobject/five-subobject invariant is applied to the total categories of the restriction splittings.

## C. Local wording and typing repairs

1. **Cross-reference identifies a construction too literally with its earlier maps.** In the endpoint application, fragment lines 293–296 say that the switching maps of `K_2` “are the lifts used in Section [arithmetic].” The earlier maps are arrows of the separately presented category `Rec`. Replace that sentence by: “The same switching construction was used in Section [arithmetic].” This is a local wording correction; the section already establishes the needed maps in `K_2`.

2. **Name the ambient category before taking a conclusion range.** In fragment lines 317–323, write: “Let `Prf` be the object of finite proofs for the rules below and `c:Prf→S` its conclusion map in `E`. Viewed as a total arrow of `A`, it has range `t₀=ran(c)`.” The existing surrounding paragraph determines the intended types, but this makes the total-category/partial-map-category passage explicit at the operation that needs it. It does not add a hypothesis or a construction.

3. **Numerical coding is required before defining an object of `K`.** The initial fragment took `D_e⊂|X|` directly as an object of `C_rec`, although the standard carriers of formal product and tagged-sum types are raw structured sets and need not literally be subsets of one finite numerical power. Merely adding `|X|=J(X)` would not repair this mismatch. The final paragraph, beginning at line 952, now uses the existing bijections `γ_X:|X|→N` and defines the numerical conjugate before assigning domains and arrows. The object assignment therefore lands in `C_rec`, the arrow assignment lands in `K`, and the inverse hom-set map conjugates back. This correction has been independently checked against Section 5's definitions. The later displayed isomorphism remains in `K`.

No other definite poor wording or empty phrase required a mathematical change. Repeated references to domains and totality have a proof function here and should not be removed merely for brevity.

## D. Coverage

| Fragment lines | Checked content |
| --- | --- |
| 1–118 | Space, cosheaf equivalence, numerical category, functor category, partial maps, frame and recursion subcategory |
| 120–147 | Local connectedness, lifting, distinction from the classical category |
| 149–249 | Evaluation and probe functors, endpoint Turing property, failure at component 0 |
| 251–396 | Parity domains, `K_2` application, initial-algebra preview, theorem/refutation sets, pair functor |
| 398–548 | Cosheaf equivalence, numerical pushout presentation, categorical versus pointwise subobjects, finite structure |
| 551–664 | Partial-map domains, ranges, joins, pullbacks, weak choice, connected restrictions |
| 666–741 | Restriction embeddings, nonempty words, frame isomorphisms |
| 743–901 | Typed Turing construction and exact-domain parameterization |
| 903–1016 | Recursion subcategory, both splitting comparisons, categorical distinction and undecidable equality |

## E. Disposition

The three repairs in C have now been incorporated and checked. The numerical-conjugation correction is a necessary typing repair, not merely a stylistic alias. No change to a theorem hypothesis or conclusion is requested. No additional elementary proof is required.

## F. Scope and uncertainty

This review did not rebuild or render the PDF, run Lean, independently reconstruct the external Heller/Curry results, or review the complete new arithmetic section. The cosheaf and fork constructions in this assigned fragment were read directly. The later initial-algebra proofs in Appendix B are outside the assigned portion; the preview's explicit structure maps and references were checked, not used as a substitute for reviewing those proofs.

Strongest confirmed defect in the assigned portion: the unannounced passage from a raw structured carrier to an object of the numerical carrier category, found in the follow-up and repaired by numerical conjugation. The switching sentence and conclusion-map typing were also corrected. Strongest suspected unresolved mathematical blocker: none identified. Recommendation for this portion: proceed to integration and compilation checks.
