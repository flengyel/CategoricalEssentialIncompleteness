# Applications and example constructions: v58 referee recheck

Reference source: the v57 snapshot at `dfe6d3b9b948875d9d268ef8bbd332d65c6b53e5`, under `review-20261114/remote/manuscript/latex`. Revised source: `revision-v58/manuscript/latex`. The comparison was performed on the literal source files, not inferred from version numbers.

## Functional outline comparison

The functional order is unchanged. Section 6 constructs the arithmetic syntax and internal derivation objects. Section 7 establishes interpretation and soundness. Section 8 applies these constructions to arithmetic, including the uniform result and the associated-category instance. Section 9 constructs computation independent of binary representation, an inseparable cut pair, internal field deduction, and the associated-category instance. Appendix B constructs the partial-map category and Turing morphism used in Section 10. Section 10 constructs the propositional and conservative first-order theories and applies the same associated-category theorem. Appendix C separates a faithful range functor from the additional lifting hypothesis. Appendix D supplies the faithful family of model interpretations and its theory-extension consequences.

All headings and all stated result labels in this scope are unchanged. Two proofs have changed: Lemma 6.1 now supplies the composition-program construction and the finite-trace argument, and Proposition B.10 changes its truth-summand reference. All remaining application source files in §§6–10 and Appendices C–D are byte-identical to the audited v57 source. Appendix B differs only at its decidable-equality definition and the corresponding sentence in B.10. Both changed proofs are reconstructed below.

## (A) Kill-shots / hard blockers

None identified. The Appendix B correction does not alter the statement or mathematical argument of Proposition B.10.

## (B) Major weaknesses

None introduced by the revision. The following interfaces were rechecked against the changed material:

- The decidable-variable hypotheses in the internal syntax constructions refer to the same truth injection `t` as Appendix A. The failure of decidable equality on the different object `V` in B.10 does not contradict the use of the constant variable object in the first-order fork construction.
- Section 9 retains the common-domain and common-value quantifiers for oracle computations. Its cut reduction and the parameterized field-deduction construction are unchanged.
- Section 10 retains the restriction to endpoints 1 and 2 for preservation of the displayed Turing morphism; the proof that central evaluation does not preserve it is unchanged.
- Corollaries 9.8 and 10.9 still cite parameterized syntax and finite derivations, regularity, partial inverses, a total reduction of an inseparable pair, and a global logical theorem. Their application of Theorems 5.2 and 5.3 is unaffected.
- Appendix C retains the distinction between finite joins of restriction idempotents and a common upper bound for two disjoint partial morphisms. The absence of the latter does not conflict with the former.

## (C) Minor issues

The prior truth-summand inconsistency is resolved.

In `appendices/b-three-point-cosheaves.tex:568–571`, decidable equality now explicitly uses the injection `t:1→Two` fixed in Appendix A. This agrees with `appendices/a-syntax-and-theories.tex:37–38` and `:130–142`, where the injections are ordered false, true and the diagonal is the inverse image of true.

In `appendices/b-three-point-cosheaves.tex:591–597`, the proof now places the endpoint equality decision in the second summand, which is exactly the true summand. No further local correction is needed.

## (D) Cross-section consistency checks

**Lemma 6.1 (`lem:arithmetized-evaluation`), reconstruction after the composition-proof addition.** The theorem statement is unchanged. At `sections/05-syntactic-recursion-category.tex:84–101`, the universal interpreter and formalized parameterization supply `u` and the primitive-recursive function `s`. A single fixed program index `c` accepts the nested input `<<f,e>,x>`, simulates `e` on `x`, and, if that halts with value `y`, simulates `f` on `y`. Consequently `comp(f,e)=s(c,<f,e>)` is primitive recursive and specializes exactly the first parameter; it leaves `x` as the remaining input. There is no circular appeal to `comp` in this construction.

The two finite input traces combine into a trace of the sequential simulator by primitive recursion on the supplied traces. Conversely, a completed simulator trace can be scanned by bounded recursion to recover the two simulated traces and their intermediate value. PA verifies those syntactic transformations and the parameterization identity uniformly in `f,e,x,z`; existentially quantifying the trace codes gives both directions of the displayed composition formula. Determinism gives functionality. For each fixed ordinary index `e`, representability of the primitive-recursive function `a↦s(e,a)` supplies the index `k_e` and its PA-provable graph and totality. This uses neither the category composition defined later nor any later Turing-morphism theorem. The new paragraph supplies the missing direct justification formerly assigned to the source citation. No changed quantifier or additional hypothesis was detected.

**Proposition B.10 (`prop:fork-distinction`), reconstruction after correction.** The constant terminal fork has five subobjects, whereas the numerical terminal singleton has two; the existing splitting equivalences therefore rule out the stated restriction equivalence. For the equality assertion, choose distinct central tuples differing only in their `z` coordinate. Their first endpoint images agree, so an equality decision at that endpoint has value true, in the second summand. Naturality forces the central decision to have that same value. Its inverse image of true is the diagonal, contradicting the distinctness of the central tuples. This argument establishes the unchanged claim with the corrected global convention.

**Corollary 4.8 interface.** The revised phrase `sections/03b-internal-adjunctions.tex:350–353` specifies universal quantification as `pi_2:V×Two→Two`. Its source and target match the algebra constructor. Since the language has only variable terms and nullary predicates, the valuation ignores term variables, gives equality value true, and is invariant under the admissible substitutions used by the proof. The displayed projection is the operation already used implicitly by the proof and by the analogous erasure argument in Proposition 10.8. This clarification introduces no additional hypothesis and changes no conclusion.

**Abstract interface.** The revised sentence `abstract.tex:14–16` says that a consistent theory with a fixed global logical theorem is essentially incomplete exactly when its constant family in the associated category is. This matches the two sides and the global-section hypothesis of Theorem 5.3 and the instances in Corollaries 9.8 and 10.9. It removes the ambiguity of “the corresponding internal theory” without enlarging the claim.

## (E) Acceptance conditions, non-negotiable

No further correction is required by this recheck. Keep the Appendix A convention and the two corrected Appendix B references synchronized. Preserve the printed common-oracle quantifiers, endpoint restrictions, and parameterized deduction hypotheses.

The review supports retaining all application claims in v58, conditional on the accepted general-theorem audit and the recorded proof statuses. It does not change an open Lean obligation to a completed one.

## (F) Not checked / uncertainty log

The v57 assignment reconstructed all 28 numbered proofs in §9, §10, Appendix B, and Appendix C; that record is in `review-20261114/examples-ledger.json`. This pass compared all 13 source files covering §§6–10 and Appendices B–D, then reconstructed both changed proofs (6.1 and B.10) and checked the relevant general-theorem and abstract interfaces. A later composition-proof addition in Lemma 6.1 was included in this final report. It did not independently repeat the unchanged arithmetic or Appendix D proofs. Their earlier audit status is retained on the strength of literal source equality, not represented as a fresh proof audit by this reviewer.

No Lean compilation, statement comparison, or axiom audit was performed in this pass. No full reread of the Knuth–Larrabee–Roberts manual was performed by this reviewer; writing conclusions from a separate complete-manual review are outside this report. No new literature or novelty search was performed.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none identified in the changed text. Most important unchecked matter in this pass: exact Lean verification status. The scoped recommendation does not depend on unavailable mathematical text. Final overall recommendation: **unknown**, since this is a revision check; within its stated scope, no new mathematical gap was found and the prior minor convention defect is corrected.
