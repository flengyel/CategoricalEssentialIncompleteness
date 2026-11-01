# Numerical-foundation consolidation, version 27

This revision implements one consolidation from the version-26 scope audit. The shared numerical foundation is proved once in §7.4. It retains explicit carrier/coding data, computable sections, partial inverses and both restriction comparison functors with their natural isomorphisms. Appendix B retains its fork-specific componentwise proofs. All applications remain.

The former combined Proposition 7.7 is divided into Proposition 7.7 (`prop:numerical-structure`) and Proposition 7.8 (`prop:arithmetic-theory-realization`). No mathematical conclusion is removed. The latter's proof and its subsequent proof-code comparison remain unchanged.

- [Change and review report](numerical_foundations_consolidation_v27.md)
- [Hostile review: initial](hostile_r1.md) and [closure](hostile_r2.md)
- [Mathematical Writing: initial](writing_r1.md) and [closure](writing_r2.md)
- [Explicit types/dependencies: initial](types_r1.md) and [closure](types_r2.md)
- [Source diff](consolidation.diff)
- [Verification record](verification.md)

The local reviews close their concrete findings. Compilation and rendering were checked separately. The manuscript is 78 pages and the standalone appendix is 10 pages. No global shortening, new whole-paper correctness audit or Lean verification is claimed.
