# Numerical limits, regular images, and terminology revision

This checkpoint starts from `69100418d5d8dd8c77a2b98a06939593aecdc51a`.
The checkout and remote `main` agreed before the constructions began; the
remote head was checked again before publication.

- [Verification result](verification.json): command results, dependency pins,
  source hashes, and 179 transitive axiom inspections.
- [Build log](build.log) and [Lean version](lean-version.log).
- [Axiom inspection](axiom-audit.log).
- [Principal declaration types](principal-statements.log).
- [Project-source proof-hole scan](source-hole-scan.json).
- [Imported comment-only comparisons](comment-only-patches.json).
- [LaTeX build log](manuscript-build.log) and [final TeX log](manuscript.log).
- [Mathematical scope review](REVIEW.md).
- [Terminology and prose review](EDITORIAL_REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

The mathematical additions construct numerical total-arrow products and their
preservation by `J`, finite limits of arbitrary PERs, regular-epimorphism/
monomorphism factorizations, and coequalizers of kernel pairs. Pullback stability
of regular epimorphisms is the next unresolved construction. Extensivity and
the arithmetic interpretation remain open.

Thirteen imported Lean files received comment-only revisions. Their original
hashes are retained in `SOURCE_PINS.json`, and their revised hashes are recorded
in `LOCAL_PATCHES.json`. The manuscript source and rebuilt PDF also have
recorded original and revised hashes. Historical audit logs are unchanged. Raw LaTeX logs retain their whitespace;
first-pass reference warnings in the build log are resolved in the final TeX log.

The documented hosted executable-path adapter was used. Ordinary Debian/WSL2
builds do not need it. Palomar Comparator, NanoDa, and con-ron were not run.
