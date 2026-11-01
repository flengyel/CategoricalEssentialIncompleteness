# Uniform family draft: dependencies and new arguments

The draft adds one subsection in the arithmetic application. It does not alter Appendix A.

Existing results used by reference:

- Lemma `lem:syntactic-total-category`: regularity, finite extensivity, and predicate objects in `B_PA`.
- Appendix A's existing logical-axiom and inference-rule morphisms: reused without their constructor grammar, side-condition definitions, or substitution proof.
- Lemma `lem:syntactic-derivation-initiality`: initial algebra for the newly specified finite rule family on `E×Fm`. Its finite-tree proof is not repeated.
- Theorem `thm:least-theorem-subobject`: least closed image; regularity gives the sentence pullback. No image-factorization proof is repeated.
- Lemma `lem:range-regular-image`: the family theorem subobject represents the range of the sentence conclusion map.
- Lemma `lem:syntactic-functional-search`: one partial proof-search program with paired input `(e,x)`; its correctness verification is not repeated.
- Proposition `prop:standard-code-soundness` and Lemma `lem:arithmetic-diagonal-representation`: soundness and the diagonal reductions in each consistent standard fiber.

The new categorical argument is special base change along a numeral point. Its complement `x ≠ ē` gives a two-summand decomposition of the parameter object. Finite extensivity identifies the slice with a product of slices. The family rule morphisms retain the parameter in all premises and the conclusion; therefore their inference endofunctor decomposes, including its nullary summand. The algebra category is a product, and components of its initial object are initial. This proves fiber initiality without assuming pullback preserves arbitrary initial algebras and without repeating numerical tree recoding.

The new uniform diagonal argument uses one partial map `ℓ:ω×ω⇀ω+ω` in the original category. The parameterized Turing property yields a total `g:ω→ω`, and `q=θ I(g):E→S` is the required total morphism in the total restriction splitting. Independence is asserted for each consistent standard presentation; no consistency decision, internal consistency predicate, or source zero reflection is introduced.
