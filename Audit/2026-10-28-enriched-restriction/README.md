# Enriched restriction objects: verification evidence

This checkpoint starts from `ea86f7d8689bcee9594ea11bd976d2265d4b76d3`.
GitHub's `main` was inspected before editing. The prior transient checkout
was unavailable, so its text sources were restored at that exact revision
and checked against their Git blob hashes. Dependency checkouts retain the
manifest revisions. No imported Lean source or dependency pin was changed.

- [Full verification result](verification.json): command exit codes,
  dependency revisions, imported-source checks, all 83 axiom results, and
  hashes of the entry point and every project module.
- [Build log](build.log).
- [Axiom audit](axiom-audit.log).
- [Toolchain version](lean-version.log).
- [Project-source proof-hole scan](source-hole-scan.json).
- [Author-side scope audit](REVIEW.md).
- [Manuscript correspondence and remaining obligations](../../FORMALIZATION_STATUS.md).

The documented hosted executable-path restriction was observed, and its
adapter was required and used. Ordinary Debian/WSL2 builds do not require it.
Palomar Comparator, NanoDa, and con-ron were not run.
