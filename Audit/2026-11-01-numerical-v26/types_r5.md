# Numerical realization: final explicit-type review

**PASS for the numerical-realization and numerical-incompleteness subsections. No unresolved type, comparison, or dependency finding remains in this review's scope.**

Final reviewed sources are frozen in `tmp/numerical26/round5/` and match the working manuscript files byte for byte:

| File | SHA-256 |
| --- | --- |
| `08c-numerical-realization.tex` | `f6606bf81ca7546b1065ae10e80e68482000ff27add2485af36ff504e879f448` |
| `08d-numerical-incompleteness.tex` | `11d6c06139fa1b2b457d3c1a577026767afae0cd2121005eac5c3ef1ed9d98f8` |
| `08-essential-incompleteness-of-arithmetic.tex` | `a67c80632f8729caa0d0679e5b8bab260a5cdc4b20636ec9399ddb23ebdc247f` |

The sole change after the fourth review aligns the description of the maps `ρ_n` with their declared codomains. The text now obtains these maps from the finite-product, coproduct, and pullback comparisons and describes them as matching corresponding rule instances. It separately uses `η_n` to compare those actual interpreted elements with the scalar predicate presentation. The previously ambiguous phrase about re-encoding directly in a predicate presentation is removed. This closes the last local finding.

The full proof-carrier conversion has explicit types at every step:

`widehat(R_n^num) → |R_n^num| → G_N R_n^syn → C_n(N)⊆N`,

using `κ_{m_n}^{-1}`, `ρ_n`, and `η_n^{-1}`. The inverse uses the three inverse maps in reverse order. The rule premise and conclusion comparisons imply that these conversions preserve valid trees and conclusions; induction gives inverse computable proof-carrier bijections. The application uses equality of their conclusion images, not literal equality of alternative stored proof codes.

The checks recorded in the preceding reports remain satisfied:

- `C_rec`, its carrier notation, both coding functors, their object and arrow actions, and their natural isomorphisms are explicitly typed. The nullary tuple object is handled by its singleton code.
- Finite limits, tagged coproducts, regular-image objects, kernel-pair descent, monomorphisms, their partial inverses, and the partial-map equivalence retain their stated source and target categories.
- The parameterized syntax and list algebras are compared with arbitrary target algebras. The folds have declared carriers, projection equations and algebra equations. Computation is proved to halt on those carriers; no total extension of target operations to all numerical inputs is assumed. Induction proves uniqueness.
- The free-variable, admissibility, and substitution maps use the established numerical algorithms with the required constructor equations. The failure-valued total substitution operation and successful substitution restriction remain distinct.
- The derivation algebra has a c.e. carrier of valid numerical trees, a typed conclusion map and structure arrow. Evaluation into any target inference algebra supplies a total fold on that carrier, preserves conclusions, satisfies its algebra equation, and is unique.
- The sentence conclusion is a declared pullback. The least-theory image theorem is cited from Appendix A instead of reproved.
- The numerical application declares the diagonal idempotents, inclusion and interpretation functors, sentence morphisms, and restriction-idempotent inequalities in their respective categories. Its passage from standard interpreted codes to the numerical category uses the proved comparison.
- The realization and incompleteness subsections have separate mathematical purposes. The new boundary preserves all required definitions and references.

This is a scoped explicit-type and dependency review of these subsections and their inspected interfaces, as detailed in the earlier reports. It is not a whole-paper certification, a new literature audit, or a Lean elaboration. No manuscript file was edited by this reviewer.
