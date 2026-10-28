# Numerical categories and support comparison: verification evidence

This checkpoint starts from `c56b783a858087f3b77f6420fd2469e9f28094e6`.
The checkout was clean and the remote `main` agreed before editing.
No imported Lean source or dependency pin was changed.

- [Full verification result](verification.json): command exit codes, dependency
  revisions, imported-source checks, 152 axiom results, and project-source hashes.
- [Build log](build.log): 1913 jobs, including cached dependencies.
- [Axiom audit](axiom-audit.log).
- [Toolchain version](lean-version.log).
- [Principal statement signatures](principal-statements.log).
- [Project-source proof-hole scan](source-hole-scan.json).
- [Author-side scope audit](REVIEW.md).
- [Manuscript correspondence and remaining obligations](../../FORMALIZATION_STATUS.md).

The seven new modules construct the numerical restriction category, the
arbitrary-PER category, the full faithful functor on total arrows, c.e. domain
supports, genuine support subobjects and their pullbacks, and c.e. categorical
joins. They prove the support form of the numerical separator equivalence.

Numerical products and preservation by `J`, remaining PER regular/extensive
structure, and syntax/provability comparisons remain open. The hosted
executable-path adapter was used; ordinary Debian/WSL2 builds do not need it.
Palomar Comparator, NanoDa, and con-ron were not run.
