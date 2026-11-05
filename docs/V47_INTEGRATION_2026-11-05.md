# Version 47 manuscript and Lean target

Version 47 is the current manuscript and Lean verification target. Commit
[`d3e741dc982a71f7f4678376eeffe945eb183d11`](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/d3e741dc982a71f7f4678376eeffe945eb183d11)
is on `main`; the remote head was checked after the update.

## Manuscript and repeated reviews

The manuscript preserves all 62 numbered results, three definitions, and 136
labels. All 33 original references were checked against primary texts. The
bibliography retains 32: Ramesh's cited work was accurate but its paragraph
supplied no comparison or dependency used by this paper. Three citation
locators were tightened.

The repeated hostile review found no demonstrated fatal or major mathematical
defect. The repeated writing review found definition-order issues for
`Par(E, Mono)` and restriction monomorphisms, repeated definitions, an ambiguous
identity antecedent, and an undeclared partial-inverse symbol. These were
repaired. Empty modifiers and defensive asides were removed. The final PDF has
73 pages, compiles without warnings, and was visually checked throughout.

The reports and complete manuscript edit patch are in `docs/reviews/`:

- `V47_REPEAT_HOSTILE_2026-11-05.md`
- `V47_REPEAT_WRITING_2026-11-05.md`
- `V47_CITATIONS_CATEGORIES_2026-11-05.md`
- `V47_CITATIONS_LOGIC_2026-11-05.md`
- `V47_MANUSCRIPT_CHANGES.patch`
- `V47_EDITORIAL_VALIDATION.json`

## Verification target

`MANUSCRIPT_CURRENT.json` selects the manuscript version, TeX entry point,
PDF, source archive, correspondence table, and audit entry points. The
verifier checks the version against the preamble, every recorded hash and
size, the assembled TeX inventory, the source archive against the active
TeX files, equality of the two PDF copies, and the correspondence-table
version. It snapshots these inputs before the Lean run and checks them again
at the end.

`CurrentStatementAudit.lean` and `CurrentAxiomAudit.lean` are the active audit
entry points. The existing `V46` implementation names remain; the current
manifest determines the manuscript target. All 1,110 existing Lean-tree
files were checked against the preceding commit and are unchanged. The two
current audit entry points are added separately.

`AGENTS.md` and `docs/CODEX_WSL2_CURRENT.txt` require later manuscript revisions
to update the target, correspondence table, artifacts, and affected Lean
statements together. The old v46 PDF, source archive, and provenance manifest
were moved into `manuscript/archive/`.

The manuscript-only check passed on the committed v47 artifacts. Temporary
fixtures accepted v47 and a correctly updated v48. Six negative cases rejected
a stale manuscript version, a changed source hash, source-archive drift, an
unassembled TeX file, a stale correspondence version, and unequal PDF copies.

## Handoff to the Lean session

Codex is responsible for Lean execution and proof development. This chat is
responsible for the manuscript. The local Lean run was stopped at the author's
scope correction, with exit status 130, during the main build. It did not reach
the strict statement checks or axiom audit. No completed full Lean verification
is reported for this run.

The manuscript-only gate passed on the committed v47 artifacts. Codex should
integrate the current main branch, use `MANUSCRIPT_CURRENT.json` and
`FORMALIZATION_STATUS_V47.md`, and run the full verifier in its existing Lean
workspace. The source gate and two current audit entry points are already
committed. No further Lean source edits are made by this chat.

The v47 correspondence table carries forward proved results and open
obligations from the preceding implementation. The editorial revision does
not change that proof status.
