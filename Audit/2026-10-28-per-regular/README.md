# PER regularity: verification evidence

This checkpoint starts from `994323256483136cfd23c3e935a826d18aa6b9cf`.
The checkout was clean and the remote `main` agreed before editing.

- [Verification result](verification.json): 191 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1922 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json).
- [Mathematical scope review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

`NumericalPER.pullback_isPullback` constructs pullbacks of represented arrows.
`pullbackSnd_regularEpi` proves stability of regular epimorphisms under these
pullbacks, and `perRegular` gives the regular-category instance. These results
supply the regularity requirement of the PER target in
`sec:integration-numerical`. Extensivity and the arithmetic interpretation
remain open.

No imported source, dependency revision, toolchain pin, or manuscript file was
changed. The hosted executable-path adapter was used; ordinary Debian/WSL2
builds do not need it. Palomar Comparator, NanoDa, and con-ron were not run.
