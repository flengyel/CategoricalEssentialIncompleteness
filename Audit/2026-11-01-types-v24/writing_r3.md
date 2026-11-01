# Mathematical-writing review, round 3

**PASS for the reviewed section and corrected passages.** No unresolved finding remains from the explicit-type and mathematical-writing reviews in rounds 1 and 2.

This verdict concerns the exact files frozen in `tmp/review24/round3/`: the complete §7.2 reviewed in round 2, its subsequent changes, and the corrected passages in §§6 and 7.1. The round-3 diff and surrounding text were read. The governing KLR source and the review criteria are recorded in `writing_r1.md`. This is a scoped editorial and type-exposition judgment, not a certification of the whole manuscript.

## Closure of the remaining findings

| Round-2 finding | Exact correction checked | Status |
| --- | --- | --- |
| The final “it” could refer to either an algebra or its underlying slice object. | The proof now states that `𝔓_e` is isomorphic **in `Alg(H_e)`** to the initial derivation algebra. A separate sentence identifies its underlying slice object. | Closed. |
| `Neg:N→N` was described only on formula codes. | The text chooses a primitive-recursive extension to all natural numbers. Its use inside arithmetic formulas still invokes the declared graph-definition convention. | Closed. |
| The soundness theorem used `ν` without a binding in its own setup. | Theorem 6.9 now declares `ν:S→S` to be syntactic negation in `B_PA`. | Closed. |

The additional changes also check:

- The inclusion functor's action is stated for a typed morphism `f:X⇀Y` in `S_PA`.
- The quasi-inverse `Ψ_e` has explicit source and target categories, object action, and morphism action with endpoints. The latter is the coproduct of the underlying slice morphisms.
- The action of `Λ_e` distinguishes an algebra morphism from its underlying slice morphism.
- The opening sentence specifies axiom sets containing the chosen sentence axioms of PA, matching the constructed family.

## Earlier findings

The round-1 corrections retained in this text give explicit ambient categories, the initial algebra's structure map, the partial inverse and its category, the numeral-complement inclusion, the restricted rule maps, the actions of `Xi_e`, the components and naturality equation of its comparison, and the transport of algebra structures. The numerical conclusion map uses named input and output presentation isomorphisms. The proof-search map uses a chosen graph index and quantified domain and output equations. The semantic substitution statement distinguishes finite expressions from their codes. The ultrapower comparison component and naturality equation have stated types.

These declarations and the cited conventions determine the sources, targets, ambient categories, and equality notions used in the reviewed arguments. Complete algebras, slice objects, and numerical presentations are distinguished at the steps where the proof passes between them.

No empty phrase or invented mathematical term was introduced by the final corrections. The organization still follows the mathematical dependencies. Appendix A's general construction proofs are used by reference; the section proves the additional family and fiber statements needed for its application.

The check is complete for this requested scope. No further editorial correction is proposed. Compilation and visual inspection of the final PDF remain the primary agent's checks; they were not performed by this reviewer.
