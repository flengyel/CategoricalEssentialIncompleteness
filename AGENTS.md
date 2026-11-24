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

Formalize the paper’s results and the mathematical inputs used to prove them.
Read the active LaTeX in recursive input order and record every mathematical
assertion, including those in the abstract, proofs, examples, remarks and
appendices. For each assertion proved in the paper, identify the Lean
declaration or proof step establishing it at the printed types and hypotheses.
For each external result used in a proof, identify the inference that uses it,
the precise statement it requires, and the checked declaration or import and
application supplying that statement. Distinguish a theorem conditional on a
hypothesis from the existence of a witness to that hypothesis.

Retain the literature discussion. For a historical attribution or comparison,
check the cited source, its hypotheses and conclusion, and the role of the
comparison in the manuscript. Record it as a source-checked attribution when
no proof uses it. The absence of a Lean proof for such an attribution does
not count as a Lean omission or proof gap. An inaccurate attribution is a
manuscript finding. If a proof invokes a result previously listed only for
comparison, record that use and check its required instance in Lean.

Have a second reader reconstruct the statements from the manuscript before
consulting the Lean declarations or the correspondence table. Compare their
types, quantifiers, and conclusions. Record and resolve discrepancies. Report
the scope of a successful Lean run by the tested commit. Claim whole-paper
formalization only after reconciling every assertion and replaying its checked
proofs at that commit.

Continue the audits until two consecutive, independent, full reports on the
same tested sources each find zero mathematical errors, zero ambiguities,
zero Lean omissions and zero proof gaps. Each report must name the tested
commit, link the whole-paper correspondence and kernel receipt, and account
for every section and appendix. An unchecked passage or missing evidence
precludes a clean report. Any finding or change to the audited manuscript,
Lean sources, correspondence or verification inputs resets the count. A
commit adding only the reports may cite the same tested revision. The second
reader must first reconstruct the arguments without the first report, then
reconcile the findings.

Preserve unrelated work. Use the existing toolchain, dependencies, mathematical
definitions, and permitted-axiom checks. Stable module or namespace names do
not determine the manuscript version.

Use `morphism` and `Turing morphism`. Define notation before use, state morphism
types, and remove empty modifiers, repeated definitions, and defensive asides.
Preserve mathematical hypotheses and substantive counterexamples.

Apply the mathematical writing standard to project-owned Lean module documentation,
docstrings, comments and declaration names. Use the term from the manuscript, the
mathematical literature or Mathlib. When the paper introduces a concept, cite
its definition at first use. Describe a construction directly if it has no name.
Keep a modifier when it distinguishes a hypothesis, construction or conclusion.
Describe the mathematics in the source and keep verification history in reports.
Check public names against their callers and the Comparator configuration before
renaming them. See Knuth, Larrabee and Roberts, [*Mathematical Writing*, §1](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).

For a Palomar release, use the [WSL2 prompt template](docs/CODEX_WSL2_PALOMAR_SUBMISSION.md#reusable-prompt). Locate and preserve the author’s requested local manuscript edition before integrating remote changes.

Commit completed changes to `main` and push them to `origin/main`.
A saved file or local commit is not completion. Before reporting completion,
verify the remote `main` commit and the active manuscript version there.
Preserve concurrent remote changes and use a non-force update. Include the
source, PDF, archive, manifest, correspondence table, and current instructions
in the same manuscript synchronization. This standing instruction also
applies to reports and later revisions.
