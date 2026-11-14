# Continuation: manuscript review and Lean formalization

Continue the project **Logical consequence and essential incompleteness in recursion categories**, repository `flengyel/CategoricalEssentialIncompleteness`. Review the manuscript from an outline, assess the forthcoming Google Deep Review report against the mathematics and sources, and continue the Lean formalization. Commit completed work promptly to remote `main`.

## Current state and authoritative files

This prompt was prepared on 14 November 2026 against remote `main` at `f0e4b78e83ea21e06b7d335bd8b72353ac25502f`. The active manuscript is **v58**. Treat this commit as a reference point; preserve any subsequent local or remote work and do not reset to it.

**Theorem 5.3 is now recorded as complete. The current count is 70 of 77 numbered results proved, with seven open.** Earlier prompts directing completion of Theorem 5.3, and earlier counts of 69 proved/eight open, are superseded. Lemma 8.9 is the next open result.

Begin by reading:

1. `AGENTS.md` and `MANUSCRIPT_CURRENT.json`.
2. The current correspondence table selected by the manifest, presently `FORMALIZATION_STATUS_V58.md`.
3. `manuscript/latex/main.tex`, all its inputs and the selected compiled PDF. Read the complete statements and standing hypotheses, not just abstracts or report summaries.
4. `docs/reviews/V58_REVIEW_2026-11-14/outline.md`, `summary.md`, `referee-core.md`, `referee-applications.md`, `writing-review.md`, the reference audit and `lean-impact.md` with its linked reports.
5. `docs/V58_ASSOCIATED_INCOMPLETENESS_2026-11-14.md`, its verification JSON and `docs/V58_THEOREM_5_3_PROOF_OUTLINE_2026-11-14.md`.
6. `docs/CEI_v58_WSL2_instructions_2026-11-14.md` and `docs/CODEX_WSL2_CURRENT.txt`. The earlier `docs/V58_LEAN_CONTINUATION_2026-11-14.md` retains detailed conventions and verification instructions, but its original Theorem 5.3 task has been completed.

The usual checkout is `/home/flengyel/src/CategoricalEssentialIncompleteness`. Inspect `git status`, fetch `origin`, and compare local and remote commits before editing. Preserve local modifications, untracked work, dependencies and concurrent proof work. The stable `V46` module prefix does not select the manuscript version. The earlier review reports retain the proof status at their dates; their references to Theorem 5.3 as open are superseded by the current correspondence and completion report.

## Google Deep Review: pending evidence

The latest manuscript has been submitted to Google Deep Review to identify omissions or errors that the repeated earlier reviews may have missed. **Its report has not yet been supplied in this conversation. Do not invent its findings or claim to have evaluated it.** Obtain the report when available. Identify the exact PDF or source version reviewed and whether the report had the bibliography and relevant appendices. Continue independent work that does not depend on the report while it is pending.

Treat every criticism as a mathematical claim to check. Neither previous review approval nor Lean compilation settles a criticism by itself. Conversely, a review assertion does not establish a defect without an argument.

For each substantive criticism:

1. Locate the exact statement and proof passage in the reviewed manuscript, then compare it with the current source. Record any version difference.
2. State the objection precisely: missing hypothesis, invalid inference, missing construction, ambiguity, incorrect attribution, novelty claim, or exposition. Identify the affected definitions and downstream results.
3. Test the strongest relevant interpretation. Supply a derivation, counterexample, explicit type comparison, or exact primary-source passage. Inspect the actual Lean theorem and its dependencies where relevant; check that its hypotheses, quantifiers, objects and conclusion match the manuscript.
4. Record the outcome as **confirmed**, **unresolved**, **answered by the existing text**, or **inapplicable to the current version**, with reasons and source locations. Split mixed objections into separate claims. Do not mark an objection answered merely because an author, plugin or previous report asserted the result.
5. Apply confirmed corrections and update all dependent statements and proofs. Keep unresolved mathematical issues explicit in the review record and correspondence table. Do not weaken a theorem silently, add its conclusion as a hypothesis, or conceal an unproved application behind an abstract interface.

Maintain a concise table with columns: review claim; manuscript location; independent check; Lean impact; disposition. Preserve the report as supplied, separately from the response. Keep this review record outside the manuscript. The article should contain the mathematics and appropriate citations, not commentary about AI reviews.

## Manuscript review and style

Work from the existing outline and revise it if the mathematical dependencies require it. Compare each section's purpose, definitions, hypotheses, theorem statements and proofs with the outline. Check the abstract and introduction against the results actually proved. Check that each application constructs the hypotheses of the general result it uses.

Use the mathematical-writing and hostile-referee reviews on proposed corrections. Follow the mathematical-writing workflow and consult Knuth–Larrabee–Roberts. Seek independent checking of substantive arguments, not repeated endorsements of the same summary. Recheck dependent passages after a correction.

Use standard mathematical terminology and economical prose in the style requested for this project. Define notation before use, give morphism types, distinguish arbitrary internal elements from standard indices, and state assumptions at their point of use. Use “morphism” and “Turing morphism.” Remove empty modifiers, repeated explanations, invented terminology and nonmathematical process commentary. Prefer inline formulas unless a display helps the argument. Use correctly typed TikZ commutative diagrams when a diagram is needed.

The v58 review checked 32 bibliography entries and 66 citation occurrences, but those checks do not exempt citations implicated by new objections. Verify each challenged or changed attribution against the primary source, including theorem numbers, hypotheses, pages and edition. Distinguish an author's result from a construction or consequence supplied in this paper. Report inaccessible evidence as inaccessible rather than claiming it was checked.

No further manuscript correction was identified by the v58 Lean impact audit. That is a scoped finding, not a guarantee that the paper has no defects. Keep v58 unchanged unless a concrete correction is established. If a mathematical revision is required, make the corresponding Lean impact explicit and synchronize the next manuscript version.

## Mathematical conventions to preserve

- General initiality is required **only for axiom subobjects**. For an arbitrary axiom morphism `a : A ⟶ S`, generation first takes `imageSubobject a`. The older all-morphism APIs have stronger explicit assumptions; use them only where those assumptions are separately justified.
- Truth is the **second coproduct injection**. The Appendix B equality convention agrees with Appendix A and `Two.point true = coprod.inr`.
- In the nullary Boolean valuation, universal quantification is the **second projection**. Retain its proved constructor equation and statement check.
- Lemma 6.1's same-evaluator PA composition identity is already proved uniformly for arbitrary internal indices. Lean uses a different choice of compiler from the proof paragraph. The existential lemma does not require literal equality of those choices; do not assert that equality or the formalization of the paragraph's specific trace transformations without proof.
- Essential incompleteness quantifies over **all closed consistent internal extensions**. For an associated category, this includes slice extensions that are not constant families. Do not replace the quantifier by a smaller class.

## Lean progress and next tasks

Theorem 5.3 was completed at proof commit `7a07264ce4137e0c539f02b30faf4d2a709fb309` and recorded on `main` at the reference commit above. The report records **25 successful incremental commands**, including 17 strict elaborations, production and statement integration, and both complete transitive axiom audits. It reports 935 current modules, 28,620 current declarations and 1,274 retained declarations. It expressly does **not** claim a new full replay.

The new proof constructs closure transport in both directions, preserves consistency and completeness for arbitrary slice subobjects, proves the full essential-incompleteness equivalence, and assembles the final reduction clause with the previously proved Boolean-morphism results. Relevant producers include `V46AssociatedClosedTheories`, `V46AssociatedIncompleteness`, `V46AssociatedSliceCoordinates`, `V46RetractedClosedTheories` and `V46SliceSubobjectPredicates`; the complete-statement check is `V46AssociatedIncompletenessChecks`.

Reuse these results. If Google Deep Review challenges Theorem 5.3, inspect the actual new types and proofs against the printed theorem; do not reinstate the earlier open status merely by copying an old prompt, and do not reject a mathematical objection merely because the status now says proved.

| Open result | Required construction |
| --- | --- |
| Lemma 8.9, `lem:arithmetic-signed-theory` | Inseparability of the arithmetic diagonal pair; internal consistency and essential incompleteness of its generated free first-order theory. |
| Corollary 8.10, `cor:arithmetic-associated-categories` | Arithmetic instance of the associated-category theorems, with the stated theory and no-total-extension witness. |
| Lemma 9.6, `lem:miller-parameterized-deduction` | Syntax and initial finite-derivation algebras for the stated semidecidable coefficients and axiom families in every Miller parameter slice. |
| Corollary 9.8, `cor:miller-associated-categories` | Miller instance of the associated-category theorems after verifying its hypotheses. |
| Proposition 10.7, `prop:fork-first-order-realization` | First-order syntax and derivation initiality in every parameter slice of the fork category. |
| Proposition 10.8, `prop:fork-first-order-conservative` | Embedding and erasure, conservativity, consistency, essential incompleteness and the endpoint conclusions. |
| Corollary 10.9, `cor:fork-associated-theories` | Associated-category application to the first-order fork theory, including the Boolean witness. |

Start with Lemma 8.9 under the printed assumption that PA is consistent. Use the existing arithmetic diagonal and syntactic derivation constructions. The remaining consistency argument uses the finite list of positive axiom labels appearing in the two proposed contradictory derivations. Construct the corresponding Boolean valuation and prove it respects both derivations, including negative axiom leaves, equality, substitution and quantification. Construct the primitive-recursive extraction and lookup operations with their PA-provable properties. Retain PA-provable disjointness of the diagonal predicates and the internal finite-list scope; an argument only about standard finite proofs does not replace the internal claim. Establish internal consistency before applying the general signed-theory incompleteness criterion. Reuse any existing inseparability proof only after checking its exact hypotheses and conclusion.

Write a proof outline and match each step to existing declarations before adding code. Do not assume the consistency or initiality that an application is supposed to construct. Complete each prerequisite before its dependent corollary. Update an open row only after every part of the printed statement has a proved counterpart and independent statement checks.

## Verification, synchronization and delivery

Preserve the pinned Lean toolchain, dependencies, provenance checks and designated isolated Palomar challenge placeholders. Production proofs and their transitive dependencies must contain no `sorry`, `admit` or `sorryAx`. Permitted logical axioms are `propext`, `Quot.sound` and `Classical.choice`.

Add complete-statement checks at the printed hypotheses and quantifiers, integrate new producers and checks through the manifest-selected entry points, and retain transitive axiom coverage. Run from the repository root:

```bash
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

The parser repair is already integrated. The manuscript-only check does not run Lean. Use the established build lock and serial Lean workflow; WSL2 previously reached 99% memory. Do not launch concurrent builds in the same checkout. Preserve logs and label interrupted, incremental and full verification accurately. Record the exact proof commit and tested input hashes; distinguish subsequent documentation changes from tested proof changes.

When revising the manuscript, synchronize the TeX sources, PDF, source archive, version manifest, correspondence table and current instructions. Compile and inspect changed pages. For proof-only work, preserve the manuscript bytes and update the proof status and evidence without a gratuitous version change.

Commit and push each completed, verified batch promptly to remote `main`, without force. Preserve concurrent changes. Do not leave several completed revisions only in a server session or worktree. Before reporting completion, compare local `main`, `origin/main` and the live remote commit, and verify the active manuscript version on the remote.

The final report should give the remote commit; the review objections confirmed, answered and still unresolved; the mathematical corrections actually made; the complete Lean results added; the verification scope and outcome; and the remaining open results. Do not claim that the whole manuscript is formalized while any of its results remains open.
