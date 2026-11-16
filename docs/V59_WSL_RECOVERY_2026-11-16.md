# WSL recovery checkpoint, 16 November 2026

The user requested saving work before exiting because VS Code cannot connect
to WSL. The WSL failure has not been diagnosed. The active Lean session was
stopped with Ctrl-C before this checkpoint was written.

The last verified production state is main commit
`0f3a24b35468854f8b3af468c85998bf8429a683`, manuscript **v59**, with **74/77**
numbered results proved. Propositions 10.7 and 10.8 and Corollary 10.9 remain
open. The latest completed incremental run has 17 commands, 9 strict
elaborations and both complete axiom audits; see
[V59_FORK_PARAMETER_COMPONENTS_2026-11-16.md](V59_FORK_PARAMETER_COMPONENTS_2026-11-16.md).
The latest completed full replay remains the earlier 1,798-command run at
`8df18834734179186459d3c4c34d4c0cf20b6194`.

## Saved work

All five new proof drafts are preserved verbatim, with SHA-256 hashes, in
[wip/V59_FORK_TRANSITION_SQUARES_2026-11-16/checkpoint.json](wip/V59_FORK_TRANSITION_SQUARES_2026-11-16/checkpoint.json).
They have `.lean.txt` extensions outside the production tree. Their original
paths are recorded in the checkpoint. Eight build and strict-check logs
are retained beside them. Production Lean sources, imports, dependencies,
manuscript, PDF, archive, manifest and correspondence table are unchanged
from the verified production state.

- `V46LaxPolynomialInputs`: product-projection and coproduct-branch laws for
  the forward polynomial input comparison. Its targeted strict elaboration
  returned zero before the interruption.
- `V46PolynomialParameterValues`: labelled-coefficient polynomial values in
  parameter slices, retaining distinct labels even when carriers coincide.
  Its targeted strict elaboration returned zero.
- `V46PolynomialParameterSquares`: the parameter-value and full slice
  comparison squares for arbitrary parameter and coefficient morphisms.
  Its targeted strict elaboration returned zero.
- `V46ForkFormulaTransitionSquares`: draft instantiation for the actual
  numerical formula algebras and fork transitions. It remains unverified.
  Kernel checks reported excessive memory consumption on the specialized
  comparison and concrete fork theorem. The latest instrumented attempt
  was interrupted. Temporary `run_cmd` stderr markers and unbounded
  heartbeat settings remain in this draft and need review/removal before
  production integration.
- `V46ForkParameterizedFormulaFolds`: an uncompiled draft of the category
  of componentwise natural parameter algebras, its literal pointwise
  product carrier, natural folds and initiality. It depends on the
  unresolved concrete constructor square. Comparison with the canonical
  `SyntaxPolynomial` parameter interface is still a separate obligation.

These drafts have no completed integrated verification, independent Checks
module, new axiom audit or full replay. They do not complete Proposition
10.7 and do not raise the numbered-result count.

## Resume after WSL is available

Read AGENTS.md, MANUSCRIPT_CURRENT.json, the selected correspondence table,
CODEX_WSL2_CURRENT.txt and its continuation documents. Fetch and reconcile
later remote and local work. Restore a selected draft to its recorded Lean
path only after inspecting the live state; retain this archive.

Use one compiler at a time under `.codex-work/build.lock`, with
`LEAN_NUM_THREADS=1` and the existing memory limit. The diagnostic builds
were reaching about 4 GB, so keep further runs bounded and interruptible.
Do not resume a background compiler merely because the drafts exist.

First inspect the concrete `relativeInput_eq` wrapper and fork theorem in
`V46ForkFormulaTransitionSquares`. Making coefficient parameters explicit
avoids recovering them by unfolding transported numerical carriers. The
generic comparison with abstract carrier objects is available, but its
specialization still causes kernel expansion. Refactor through abstract
algebra records or explicit normalization lemmas, rather than weakening
any printed hypothesis. The archived source contains the latest explicit
arguments and profiling instrumentation.

After the source constructor square checks, verify the global fold draft
for arbitrary target families and every natural algebra morphism. Do not
replace the concrete source square by a hypothesis. Remove diagnostics,
add independent statement checks, integrate current entry points and full
axiom coverage, and update the correspondence only to the actual proved
scope. Stable lists, occurrence/substitution/sentence constructions and
finite derivations for axiom subobjects in every parameter slice remain
open. Preserve the Boolean conventions, permitted axioms and pinned
dependencies. Commit verified batches promptly, push without force and
verify live remote main before reporting completion.
