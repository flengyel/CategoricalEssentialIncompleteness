# Boolean-presentation verification evidence

This checkpoint starts from `639edbafe31cbe84122ec532cca1818f3d7257b5`.
The existing checkout was clean, and GitHub's `main` agreed before editing.
No imported Lean source or dependency pin was changed.

- [Full verification result](verification.json): command exit codes,
  dependency revisions, imported-source checks, all 33 axiom results, and
  hashes of the entry point and every project module.
- [Build log](build.log).
- [Axiom audit](axiom-audit.log).
- [Toolchain version](lean-version.log).
- [Project-source proof-hole scan](source-hole-scan.json).
- [Author-side scope audit](REVIEW.md).
- [Manuscript correspondence and remaining obligations](../../FORMALIZATION_STATUS.md).

The existing hosted executable-path adapter was required and used as described
in [HOST_BUILD.md](../../HOST_BUILD.md). Ordinary Debian/WSL2 builds do not
require it. Palomar Comparator, NanoDa, and con-ron were not run.
