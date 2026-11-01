# Hostile-referee recheck of the main-paper repairs

Scope: only `tmp/review29/main_repairs.diff` and its current source context in *Logical consequence and essential incompleteness in recursion categories*. This closes the prior findings and checks the listed repairs; it is not another whole-paper audit.

## (A) Kill-shots / hard blockers

None confirmed. Scoped pass clear.

## (B) Major weaknesses

None confirmed in the repairs.

## (C) Minor issues

No required finding remains in the rechecked passages. The opening now states the categorical conclusion, and Appendix C no longer verifies the three unused target properties.

## (D) Cross-section consistency failures

None confirmed. Checks performed:

- Proposition C.1 now existentially quantifies the Turing morphism `tau_K:N x N ~> N` and isomorphism `b:N -> N+N`, and explicitly defines both restriction idempotents on `N`. The proof supplies those same choices. The counterexample's conclusion is unchanged.
- Appendix C retains the relevant total inverse-image union law, nonzero target identity, and proof that the particular target conditional has no source lift. Deleting the unused splitness, local-connectedness, and weak-choice observations removes no premise of that argument.
- The introduction now says “inseparability of restriction idempotents”. Its roadmap follows the manuscript's actual section order and distinguishes Appendix D from the interpretation section. All newly referenced labels exist.
- Appendix D supplies the typed source morphism `ell_c:U -> U+U` and its two equations before citing the range-functor, nonzero-identity, and target join hypotheses. These are exactly the premises of Corollary 3.3. The theory-extension argument is unchanged.
- The endpoint application names `c,c':W ~> W` in `K_2` and `ell_c:W -> W+W`, and states the two required equations. Its numerical construction applies because the carriers of `K_2` are recursively coded objects and the subcategory is full. The reference to the numerical incompleteness subsection avoids repeating the program proof.
- The new `sec:numerical-incompleteness` label is an additional label on the existing subsection; it introduces no new mathematical object or dependency.
- In Section 3, “the agreement law for ranges” denotes the law explicitly stated in Section 2. Replacing “exchange the coproduct tags” by agreement with opposite injections changes no equation or hypothesis.

## (E) Acceptance conditions, non-negotiable

None outstanding within this recheck. No additional polish iteration or mathematical reconstruction is required by these findings. No theorem or application must be dropped.

## (F) Not checked / uncertainty log

No fresh full-manuscript review, literature verification, Lean checking, compilation, or visual inspection was performed by this reviewer. Those are outside the requested repair recheck. The unchanged initial-algebra, arithmetization, and Turing-morphism constructions have not been recertified.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none identified in the rechecked changes. Most important unchecked material: the unchanged mathematical constructions outside this scope. The scoped conclusion does not depend on unavailable material. Final recommendation: **unknown** for the full manuscript; **no required findings remain in the scoped repairs**.
