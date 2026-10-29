# Numerical recursion category and indexing: verification evidence

This checkpoint starts from `06f4e14ea2ce77bc57afd0f72068026a95466c69`.
The checkout was clean and the remote `main` agreed before editing.

- [Verification result](verification.json): 336 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1949 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json): 60 Lean files.
- [Mathematical scope review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

`Numerical.natIso` and `totalNatIso` give recursive isomorphisms between `ℕ`
and each numerical object, in the partial and total categories respectively.
Their inverse equations use the actual partial maps restricted to the
specified source carriers. `numericalIsotype` follows.

`Numerical.turingEvaluator_isTuringMorphism` proves the Turing factorization
property for every numerical parameter object. Computable partial application
of program codes gives the required total parameter arrow. Together with
isotype, this constructs `numericalRecursionCategory`.
`turingIndexing_evaluation` proves the evaluation equation for a function on
extensional sets of arrows, obtained by choosing a code for each partial arrow.
All names in this paragraph are in `Numerical`.

These constructions supply the numerical recursion category in
`sec:integration-numerical` and the set-level indexing function. The
Set-enriched structure, its internal indexing morphism, and the arithmetic
syntax, representation, and quotient comparisons remain open.

All 311 previous axiom checks are retained. No imported source, dependency
revision, toolchain pin, or manuscript file was changed. The hosted
executable-path adapter was used; ordinary Debian/WSL2 builds do not need it.
Palomar Comparator, NanoDa, and con-ron were not run.
