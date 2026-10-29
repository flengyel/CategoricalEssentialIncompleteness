# Numerical Boolean arrows and complemented subobjects: verification evidence

This checkpoint starts from `f51ca8e82ba08603f206f51f1ec1b37ad047e45d`.
The checkout was clean and the remote `main` agreed before editing.

- [Verification result](verification.json): 273 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1936 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json).
- [Mathematical scope review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

`NumericalPER.booleanIso` identifies the chosen coproduct of terminal objects
with the explicit Boolean PER; `booleanIso_point` proves both point equations.
`booleanArrowEquiv` identifies its arrows from `D_ℕ` with total recursive
Boolean functions, and `booleanArrow_boundFiber` identifies their categorical
fibers with support inclusions. `isComplemented_iff_recursive_support`
characterizes every complemented subobject of `D_ℕ`.

`Numerical.isComplemented_iff_represented_domain` expresses the characterization
through complementary numerical domain pairs, and
`isComplemented_domainSubobject_iff` reflects existence of a complement.
The general categorical statement
`isComplemented_iff_exists_characteristic` uses regularity and finite
extensivity, which are already proved for the PER category.

These results complete `lem:integration-numerical-subobjects` together with
the preceding support and predicate constructions. Numerical restriction
products, recursion/indexing, and the arithmetic interpretation remain open.
No imported source, dependency revision, toolchain pin, or manuscript file was
changed. The hosted executable-path adapter was used; ordinary Debian/WSL2
builds do not need it. Palomar Comparator, NanoDa, and con-ron were not run.
