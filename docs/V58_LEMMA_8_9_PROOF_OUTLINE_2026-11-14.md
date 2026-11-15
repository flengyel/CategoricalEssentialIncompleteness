# Lemma 8.9: construction outline

Target: `lem:arithmetic-signed-theory` in manuscripts v58 and v59,
`sections/08-essential-incompleteness-of-arithmetic.tex`, under the printed
assumption that PA is consistent. The manuscript and its 77 result statements
are unchanged. This outline concerns the remaining construction; it does not
change the recorded 70 completed numbered results.

1. **Diagonal pair.** Use `ArithmeticDiagonalCodes.a0` and `a1`, their proved
   arithmetic representations, and the source conditional construction.
   Check the transfer to `Split(S_PA)` at the actual restriction idempotents.
   The contradiction uses nontriviality from consistency of PA.
2. **Nullary syntax and signed axioms.** Use the constructed parameterized
   syntax and derivation algebras. `SignedFirstOrder.axioms` is the join of
   the positive and negative atomic images; `SignedFirstOrder.theory` is
   its generated closed theory. Generation remains indexed by axiom
   subobjects. Identify this object with the printed theory before applying
   any general incompleteness theorem.
3. **Internal induction.** `StandardInduction.derivation_constructor_cases`
   and `typed_children_smaller` already hold in every arithmetic model.
   The existing `nat_rule_induction` quantifies only over standard codes.
   Derive induction for arithmetically definable predicates in every PA
   model, using internal arithmetic induction on the actual numerical
   node count. Do not assume external well-foundedness of a nonstandard
   model or preservation of initial algebras by interpretation.
4. **Finite lookup.** Use the existing canonical vector encoding and
   Foundation's Delta-one membership formula. Construct the total functional
   Sigma-one lookup graph, with output one for membership and zero otherwise.
   Prove the model equations at arbitrary internal vector lengths and obtain
   the corresponding PA theorems. Prove primitive recursiveness on the
   standard codes through the existing `NatVectors` comparison. Numerical
   zero/one outputs require a separate comparison with categorical Boolean
   injections; the true injection remains the second injection.
5. **Positive support.** Extract the positive nonlogical leaf labels from
   each actual derivation tree and concatenate the two lists. Prove that
   every extracted label satisfies alpha, and that every positive leaf in
   either tree occurs in the combined list. This extraction must be defined
   on the existing codes, with PA-provable equations, not on a replacement
   external proof datatype.
6. **Valuation and consistency.** In the parameter slice over the combined
   support, instantiate `NullaryBooleanValuation`: equality has value true,
   negation and implication have their Boolean values, and universal
   quantification is the second projection. Reuse its admissible-substitution
   and seven-scheme soundness proofs. PA-provable disjointness of alpha and
   beta makes each negative leaf true. Internal induction proves truth of
   both proposed contradictory conclusions and rules them out in every PA
   model. Convert this PA theorem to the actual generated-theory subobject
   equation. Standard-code soundness alone is insufficient.
7. **Essential incompleteness and application.** Apply
   `SignedFirstOrder.essential_incomplete_iff_inseparable` only after the
   constructed consistency proof and the subobject/domain comparisons are
   available. Keep Lemma 8.9 open until all its clauses have independent
   statement checks. Corollary 8.10 then instantiates the completed
   associated-category theorems with all extension quantifiers unchanged.

Each implemented step requires strict elaboration and transitive axiom checks.
Supporting steps do not discharge the numbered lemma. The supplied Google review is assessed separately in
`docs/reviews/GOOGLE_V58_2026-11-14/assessment.md`. Its approval does not
complete an open Lean construction.
