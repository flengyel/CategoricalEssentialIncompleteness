# Project instructions

Lean verification targets the current manuscript in `manuscript/latex/`.
`MANUSCRIPT_CURRENT.json` selects its version, PDF, source archive,
correspondence table, and audit entry points.

When revising the manuscript, update that manifest and the correspondence
table in the same change. Update any affected Lean statements and proofs,
rebuild the manuscript, regenerate its source archive, and run verification.
This applies to version 47 and every later revision. An earlier version may
remain in the archive; it is not the active verification target.

Keep existing proof status accurate. A prose revision does not turn an open
proof obligation into a proved result. A changed mathematical statement
requires a corresponding Lean proof or an identified open obligation.

Preserve unrelated work. Use the existing toolchain, dependencies, mathematical
definitions, and permitted-axiom checks. Stable module or namespace names do
not determine the manuscript version.

Use `morphism` and `Turing morphism`. Define notation before use, state morphism
types, and remove empty modifiers, repeated definitions, and defensive asides.
Preserve mathematical hypotheses and substantive counterexamples.

Commit completed changes to `main` and push them to `origin/main`.
A saved file or local commit is not completion. Before reporting completion,
verify the remote `main` commit and the active manuscript version there.
Preserve concurrent remote changes and use a non-force update. Include the
source, PDF, archive, manifest, correspondence table, and current instructions
in the same manuscript synchronization. This standing instruction also
applies to reports and later revisions.
