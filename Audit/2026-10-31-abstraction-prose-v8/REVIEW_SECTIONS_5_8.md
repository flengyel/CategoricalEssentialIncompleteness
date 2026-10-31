# Independent review of revised Sections 5–8

**Source and scope.** `tmp/v8_sections5_8.tex`, read in full, including the final repairs reported by its author. This is an independent review of the fragment's mathematical types, changes of representation, cited standard evaluator construction, and revised arguments. The original v7 definitions and Appendix B were consulted at the relevant dependencies. No manuscript edits were made by this review. No compilation, PDF inspection, Lean verification, or push is claimed.

Reviewed final fragment: 603 lines; SHA-256 `194ca0fd333d161bb6ec88239b040a781fb6e994df87a81e0d623a30fdb8aa56`.

## A. Hard blockers

None confirmed in the final fragment. In particular, the syntactic evaluator is no longer obtained by an unqualified appeal to a “universal program.” The lemma names the numerical index and parameter operations, states their PA-provable graph identities, and the subsequent argument passes to arrows of the quotient category explicitly.

## B. Substantive assessment

The revised specification is sufficient for the uses made of the evaluator. The standard numerical types, their carriers, and their coding bijections are fixed separately. The numerical functions `s, comp:N²→N` and the index `u∈N` are not called categorical morphisms. The categorical morphisms are then `τ_T=[u]_T` and `r=[k_e]_T` with their source and target types stated. The PA-provable graph identity implies the required equation in `S_T`; it is not inferred merely from standard denotational equality.

The replacement of the extended trace argument by the precise Montagna references is appropriate. Montagna, printed p.108, explicitly identifies the evaluator induced by `(e,x)↦φ_e(x)` and derives its Turing property from formalized s-m-n. Printed p.115, Note 1, fixes the Kleene trace and output formulas. These supplied primary passages were reread. Di Paola–Montagna, printed p.644, explicitly describes the conservative use of primitive-recursive extensions and expansion back into PA; that passage was also reread. The lemma states the particular standard identities needed here, without requiring a new interpreter implementation or a duplicate proof of formalized recursion theory.

The model interpretation correctly inserts `γ_X^M` and `γ_Y^M` into the graph formula, and the composition proof explicitly converts the intermediate arithmetic code by the inverse bijection. Model parameters range over `|M|`, not over the standard index set. The failure of target universality uses countability at one model coordinate and the displayed singleton-family parameter object.

The numerical application defines `φ_e` by standard interpretation, then defines `Rec` with those actual partial functions as arrows. Its carrier functor is separately named. The isomorphism from `S_Th(N)` to `Rec` is stated only for true arithmetic. No denotation functor for arbitrary merely consistent `T` is introduced.

## C. Local findings and disposition

All local findings raised during this review are resolved in the final fragment:

| Anchor | Finding | Final disposition |
| --- | --- | --- |
| §5, range argument following `eq:domain-order` | The running arrow and competing arrows required their common source and target types. “Receives” suppressed the relevant equation. | Now `[e]_T:X⇀Y`, `[C]_T:Y⇀Y`, and `g=[p]_T,h=[q]_T:Y⇀Z`; the equation `[C]_T[e]_T=[e]_T` is explicit. |
| §5, evaluator lemma and composition definition | The first draft duplicated the composition display and contained a long trace verification. | The standard proof is cited precisely, and composition is explicitly defined by `[f]_T[e]_T=[comp(f,e)]_T`. The old `eq:composition` reference is retained on the lemma's composition identity. |
| §6, `eq:model-functor` | Bind the interpreted arrow and the two arguments at the point where the displayed partial function is defined. | The display now specifies the typed index and `x∈X_M`, `y∈Y_M`. |
| §8, opening of the splitting application | Concrete sentence and proof carriers needed an explicit formal split-object convention. | A c.e. `D⊂N` now denotes `(ω,1_D)`; numerical representatives, their domain/image conditions, and totality are specified. The comparison construction is cited in Appendix A. |
| Same paragraph | The target carrier `E` appeared without a c.e. hypothesis. | It is now explicitly a c.e. subset of `N`. |

No remaining mathematical correction is requested. The total type `κ_n:ω→ω` and its PA-provable constant graph are explicit. In the splitting application the already declared numerical-carrier convention applies to `S`, `Prf_T`, and `N`; the categorical conclusion map and its range are typed. The proof-object reference is correctly to an initial-algebra **and pullback** characterization, so it does not assert that the sentence-restricted object alone is the derivation algebra.

## D. Cross-section checks

1. The definition of `Q_{T,T'}` preserves the graph-defined restrictions and ranges, and its surjectivity on hom-sets justifies the preservation of any Turing morphism used in the corollary. Its action is on quotient classes, while the product projection acts on model-coordinate families.
2. The switching proof derives its graph equation and totality in `T`. It does not assert that PA proves the arbitrary complementary-domain predicates exhaustive. The typed coproduct comparison accounts for the section's target.
3. The arithmetic pair is first a pair of restriction idempotents on `ω`; the text then identifies the numerical sets and their recursive inseparability. The full functor `I:Rec→Split(Rec)` preserves the separator problem on the original object.
4. The `Pair(Rec)` definition uses subsets of `J(X)` and acts on those subsets through `J(f)`. It does not treat a formal type itself as a set.
5. Revised Appendix A's comparison `Q_num` was cross-checked against the new carrier convention. Raw product/tagged carriers `|X|` need not literally be c.e. subsets of a single numerical power. The final Appendix A fragment therefore uses `hat f=γ_Y∘J(f)∘γ_X^{-1}:N⇀N` and domain subsets of `N`. This resolves the actual target-object typing issue and agrees with Sections 5–8.

## E. Disposition

The revised Sections 5–8 are ready for integration on the evidence of this review. No further expansion of elementary coding or trace proofs is required. The displayed types, quotient equations, coding comparisons, and exact Montagna references provide the data relevant to the stated categorical arguments.

This disposition is limited to the reviewed fragment and the dependencies identified above; it is not a whole-manuscript or formalization certification.

## F. Uncertainty and limits

The Montagna and Di Paola–Montagna passages identified in B were independently read in the supplied primary texts. Di Paola–Montagna's Corollary 4.4 on printed pp.657–658 was also checked against the local-connectedness citation. Bernardi's numerical precompleteness paragraph and the separately cited failure-of-composition result were not freshly reconstructed from their primary sources in this pass; their claims are unchanged in mathematical content, and this review found no new contrary evidence. No claim is made to have formalized the standard arithmetization theorem or verified compiled Lean code.
