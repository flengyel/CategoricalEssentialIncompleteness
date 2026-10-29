# PER coproducts and extensivity: verification evidence

This checkpoint starts from `9d9f2e4d1be9c83a74c155377053917cc40e703f`.
The checkout was clean and the remote `main` agreed before editing.

- [Verification result](verification.json): 213 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1926 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json).
- [Mathematical scope review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

`NumericalPER.coproductIsColimit` gives binary coproducts. `decompositionIso`
identifies the coproduct of the two inverse images with the source.
`perFinitaryExtensive` proves finite extensivity, and `coproduct_disjoint` gives
disjointness. Combined with regularity, these results supply the target-category
structure in `sec:integration-numerical`.

No imported source, dependency revision, toolchain pin, or manuscript file was
changed. The hosted executable-path adapter was used; ordinary Debian/WSL2
builds do not need it. Palomar Comparator, NanoDa, and con-ron were not run.
