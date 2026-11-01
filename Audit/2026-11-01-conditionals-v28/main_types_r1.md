# Version 28: application types and dependencies, first review

Scope: the new complementary-conditionals corollary and its uses in the proposed version-28 manuscript, compared with `tmp/move28/baseline` (version 27). This is a source-level type and dependency review, not a full correctness review or Lean verification. No manuscript files were edited by this reviewer.

## Mathematical checks

The new `cor:source-conditionals` correctly derives source inseparability from the existing comparison theorem and its lifted-separator corollary. For complementary `c,c'` on `U`, the identities `ell_c c = i_1 c` and `ell_c c' = i_0 c'` imply `epsilon_0 ell_c = i_0 c'` and `epsilon_1 ell_c = i_1 c`. The two sides agree after `c,c'`, hence after their copairing, whose range is `1_U`; range agreement gives the equalities. Taking restrictions gives the required swapped inverse images. With `P=F(c)`, `N=F(c')` and `s_c=chi^{-1}F(ell_c)`, the types and orientation match `cor:separator`. Nonzeroness and total inverse-image preservation of joins remain explicit. Neither local connectedness, target splitness nor weak choice is used.

The concrete applications supply the source conditional:

- **Syntactic category/model functor:** Lemma `lem:switch` gives the same total source program for every model. Proposition `prop:model`, nonempty model carriers and preimages of unions supply the remaining hypotheses.
- **Numerical recursion:** the existing recursive branch function has the displayed restrictions to `c,c'`. The actual-function range functor and target preimage law are explicitly retained, and its identity is nonzero.
- **Miller:** the two membership computations belong to the same source category `E_a`. Their domains are independent of the binary representation, disjoint and covering. One parallel-search program therefore has a fixed output tag and input value for every representation. The target `K_p` preimage and nonzero facts remain. The oracle version of this argument supports the later failure-of-Turing-preservation contradiction. The compactness/unanimity proof of the Turing morphism remains intact.
- **Cosheaves:** complementary domain inclusions have a componentwise computable coproduct inverse; naturality of that inverse is displayed with the correct sources and targets. The copairing `ell_c=[i_1m,i_0m']q^{-1}:V -> V+V` is total and lies in the full source category. The inclusion range functor, nonzero identity and join law are stated. Endpoint comparison retains the full numerical subcategory, its Turing morphism, actual-function range functor and total recursive conditionals.
- **Faithful model family:** the single source conditional interprets coordinatewise. The already proved range-functor, nonzero and union-preservation facts support the new corollary. Theory extension preserves the defining operations and the argument remains typed.
- **Appendix C:** with `P=F(1_A)` and `N=F(1_{A^c})`, the displayed conditional has its first-summand inverse image `N` and second-summand inverse image `P`. Its missing lift is a counterexample concerning the general comparison theorem, independently of local connectedness.

## Local findings

1. **Appendix C, opening.** The first replacement referred to the “lifting hypothesis” of `cor:separator`. That corollary states nonexistence of a pair `(s,ell)`; an existence-of-lift premise occurs instead in `thm:comparison`. Refer to the comparison theorem, or state directly that the target conditional need not lift. This is a local reference/scope error, not a failure of the counterexample.
2. **Appendix C, Proposition `prop:missing-lift`.** Replacing the former omnibus hypothesis reference dropped the explicit assertion that `F` is a range functor. The proof still verifies it. State “a faithful range functor” in the proposition.
3. **Introduction, paragraph after the new opening.** The sentence “Joins ... suffice for lifting” can be read as asserting that an arbitrary target morphism in the comparison theorem lifts. The retained proposition proves the existence of source complementary conditionals. Say that the joins “supply these total morphisms” or “supply complementary conditionals”.

Findings 1–2 were repaired during this review. Finding 3 was sent to the parent for a narrow clarification. No further mathematical or typing defect was found in the inspected replacement arguments.

## Preservation checks

Independent byte comparisons with the version-27 baseline establish:

- Entire internal-theory construction, syntactic recursion-category presentation, syntactic realization, indexed theory-family and uniform-independence files are unchanged.
- Entire consolidated numerical realization and arithmetic code-comparison file is unchanged.
- Appendices A and B are unchanged, including the cosheaf local-connectedness proof.
- The model-interpretation file is unchanged from “The total interpretation functor” onward, preserving the substitution, standard soundness and ultrapower comparisons.
- The numerical arithmetic file is unchanged from the actual theorem-domain application onward.
- The Miller first-order field-theory realization and its incompleteness argument are unchanged.
- The cosheaf propositional construction and subsequent theory/observation arguments are unchanged.

A literal-label scan found no unresolved `ref`/`eqref`/`autoref`/`cref` labels and no remaining reference to the moved local-connectedness theorem or its preparatory lemmas. Remaining assertions of local connectedness are proved categorical properties, not dependencies of the logical conclusions.

Compilation, rendered-page inspection and the independent note's mathematics are outside this review's scope.
