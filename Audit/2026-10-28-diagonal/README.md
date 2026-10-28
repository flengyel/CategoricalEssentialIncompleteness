# Diagonal and quotient verification evidence

This checkpoint starts from `08e094d7c3e923eb690b66b5fce5ac85f724b636`.
The existing checkout was clean and GitHub's `main` matched that revision
before editing. No imported Lean source or dependency pin was changed.

- [Full verification result](verification.json): command exit codes,
  dependency revisions, imported-source checks, all 26 axiom results, and
  hashes of the project entry point and every project module.
- [Build log](build.log).
- [Axiom audit](axiom-audit.log).
- [Toolchain version](lean-version.log).
- [New-source proof-hole scan](source-hole-scan.json).
- [Author-side scope audit](REVIEW.md).
- [Manuscript correspondence and remaining obligations](../../FORMALIZATION_STATUS.md).

The existing hosted executable-path adapter was required and used as described
in [HOST_BUILD.md](../../HOST_BUILD.md). Ordinary Debian/WSL2 builds do not
require it. Palomar Comparator, NanoDa, and con-ron were not run.
