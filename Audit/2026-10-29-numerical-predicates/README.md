# Numerical predicates and domain embedding: verification evidence

This checkpoint starts from `43ef82666d9919cdea35f1a59bd0557f450a6830`.
The checkout was clean and the remote `main` agreed before editing.

- [Verification result](verification.json): 247 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1931 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json).
- [Mathematical scope review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

`Numerical.domainPredicates` and `Numerical.predicates` construct the two
predicate functors. `Numerical.domainEmbedding` is their injective natural
bounded lattice map. `Numerical.predicateSubobjectIdentification` identifies
the latter functor with the full subobject lattices along `toPER`.
`Numerical.domainSubobject_isCompl_iff` preserves and reflects complementarity
of a specified pair. The generic `subobjectPredicates` construction uses only
regularity and finite extensivity.

These results prove the natural bounded lattice embedding assertion of
`lem:integration-numerical-subobjects`. Its Boolean-fiber and complemented-
subobject characterization remains open, as does the arithmetic interpretation.
No imported source, dependency revision, toolchain pin, or manuscript file was
changed. The hosted executable-path adapter was used; ordinary Debian/WSL2
builds do not need it. Palomar Comparator, NanoDa, and con-ron were not run.
