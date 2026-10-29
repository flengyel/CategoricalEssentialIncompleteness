# Numerical enrichment and global comparisons: verification evidence

This checkpoint starts from `fcea3cce61067fdad81796f0d4a31cd46b09054e`.
The checkout was clean and the remote `main` agreed before editing.

- [Verification result](verification.json): 383 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1956 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json): 67 Lean files.
- [Mathematical scope review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

`Numerical.enrichedRestriction`, `enrichedProducts`, and `enrichedZeros`
internalize the numerical partial-arrow operations in `Type`.
`enrichedDomainLattices` constructs the bounded distributive lattices on the
actual chosen domain equalizers, with their required equations for every
parameter type and every partial-arrow family. `enrichedTotalEquiv` identifies
the actual totality pullbacks with numerical total hom-sets. All names in
this paragraph are in `Numerical`.

`Numerical.internalIndexing_evaluation` proves that internal indexing is a
section of evaluation. `internalEvaluation_composition` identifies this
evaluation with internal composition and partial pairing using the Turing
evaluator. `enrichedPredicateEmbedding` gives the monic natural embedding
into full PER subobject predicates. All names in this paragraph are in
`Numerical`.

`Numerical.enrichedGlobalEquivalence` and `enrichedGlobalTotalEquivalence`
compare the global partial and total categories with the existing numerical
ones. The functor `enrichedToPER` preserves binary products, and
`enrichedPredicateSubobjectIdentification` supplies the natural identification
with the genuine PER subobject functor. `enriched_domainSubobject_apply`
identifies the resulting domain map with numerical support inclusion. All
names in this paragraph are in `Numerical`.

The numerical enriched data in `cor:numerical-definability-algebras` are
constructed. Effective syntax, the theory-specific representation section,
the Lindenbaum presentation, and the extension and arithmetic comparisons
remain open.

All 336 previous axiom checks are retained. No imported source, dependency
revision, toolchain pin, or manuscript file was changed. The hosted
executable-path adapter was used; ordinary Debian/WSL2 builds do not need it.
Palomar Comparator, NanoDa, and con-ron were not run.
