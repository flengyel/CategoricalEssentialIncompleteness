# Outline: finite proof algebras in range restriction categories

## Mathematical question

Which explicit computational structure constructs the syntax, finite proofs,
and theorem domains needed for an essential-incompleteness argument?

## Sections

1. **Computational domains and inseparability.** Define restriction domains,
   range operators, universal ranges, restriction products, complementary
   separation, consistency, and completeness. Proposition 1.1 uses parameter
   universality and binary case distinction to construct an inseparable pair.
2. **Initial algebras from domains and partial folds.** Define the lifted
   restriction functor on total split objects, Heller agreement unions, coding
   inverses, and stages e₀=0, eₙ₊₁=γP(eₙ)δ. Theorem 2.1 proves initiality from
   the two specified domain unions and exact-domain partial-fold gluing.
3. **Typed constructor maps from a universal object.** Define the partial slice
   and inference polynomial, including its action on arrows. Universal ranges
   turn partial retractions into restriction inverses. Universal-object
   dominance gives typed coding maps. Corollary 3.3 proves parameter stability.
4. **Turing morphisms and partial folds.** Lemma 4.1 proves parameterized
   recursion. The range of the diagonal filters the universal evaluator to
   respect expression types. Polynomial strength is used only for total program
   parameters. Theorem 4.2 constructs h=αP(h)δ; restricting h to the stage union
   discharges the gluing assumption of Theorem 2.1.
5. **The uniform numerical instance.** Uniform dovetailing supplies the domain
   unions and parameterized folds. C.e. instance carriers are allowed.
   Proposition 5.1 verifies regularity, extensivity, regular-image agreement,
   and decidable equality in the total split numerical category.
6. **A categorical construction of a consistent presentation.** Define lists,
   classical syntax, three Hilbert axiom schemes, and modus ponens. Lemma 6.1
   identifies the least rule-closed domain as the range of the proof-conclusion
   map. Theorem 6.2 proves consistency by valuations parameterized by finite
   positive-leaf lists. Corollary 6.3 proves incompleteness of every consistent
   computational extension when the atomic domains are inseparable.
7. **Presheaf completion and the range obstruction.** Cite Heller's existing
   counterexample. Recall the selected-subobject isomorphism of Garner–Lin.
   Proposition 7.1 shows that a specified externally indexed coproduct has no
   selected range. Problem 7.2 asks for finite-stage domain unions from
   categorical iteration and for categories satisfying the logical hypotheses.

## Dependencies that must remain explicit

- The Turing morphism supplies both the inseparable pair and the partial folds.
- Universal-object dominance and universal ranges supply typed constructor
  embeddings; universal ranges also supply the evaluator's equality filter.
- The finite-stage theorem assumes that e is the agreement union of eₙ and
  P(e) is the agreement union of P(eₙ). Parameterized application requires
  stability of these unions under restriction products.
- The sufficient polynomial-preservation argument separately uses preservation
  by restriction products, total inverse image, and finite coproducts. Product
  stability alone is not claimed to imply all these conditions.
- The Turing fixed-point equation does not identify the fold's entire domain
  with the union of finite stages. It produces an upper bound, then he gives
  exactly that domain once the union e exists.
- Consistency uses regularity, extensivity, range/regular-image compatibility,
  decidable atom equality, and parameter-stable lists, syntax, and proof
  algebras. It does not assume a global computable separator of the axiom pair.
- Incompleteness uses total inverse-image preservation of complementary
  domains. No soundness hypothesis on an arbitrary extension is used.
- Range/regular-image compatibility forces every total-category subobject to
  be computational up to isomorphism. It cannot be silently imposed on a larger
  presheaf category with a proper selected class of admissible subobjects.

The general stable-domain-union construction, nonnumerical examples meeting all
hypotheses, and the arithmetic comparison are not supplied by this supplement.
