# Numerical restriction products and comparisons: verification evidence

This checkpoint starts from `7befddd873d85750721aafb2f47f913cda082ddf`.
The checkout was clean and the remote `main` agreed before editing.

- [Verification result](verification.json): 311 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1941 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json).
- [Mathematical scope review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

`Numerical.numericalPCategory` and `numericalProdominical` supply the
restriction-product and zero-absorption structure of the numerical category.
`inducedRestriction_eq` identifies the induced restriction with the original
numerical structure. The proof does not require a terminal object, domain
splittings, complements, or a recursion hypothesis.

`pcategoryTotalEquivalence` compares the two total-arrow categories, and
`fromPCategoryTotal_pairing` identifies their pairings. `totalPair_eq_lift`
and `toPER_totalPair` give the comparisons with the existing numerical and
PER products. `domainOrderIso` identifies the domain presentations, and
`numericalDomainJoins` constructs the required joins from c.e. unions.
`domainComparisonHom` is bijective and preserves partial inverse image.
All names in this paragraph are in `Numerical`.

These constructions supply the numerical restriction products in
`sec:integration-numerical`. Isotype, the Turing morphism, indexing,
Set-enrichment, and the arithmetic interpretation remain open.
No imported source, dependency revision, toolchain pin, or manuscript file was
changed. The hosted executable-path adapter was used; ordinary Debian/WSL2
builds do not need it. Palomar Comparator, NanoDa, and con-ron were not run.
