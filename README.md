# Logical consequence and essential incompleteness in recursion categories

The current manuscript and new Lean formalization target are **version 46**,
dated 2 November 2026.

| Item | Location |
| --- | --- |
| Current PDF | [logical_consequence_and_essential_incompleteness_v46.pdf](manuscript/logical_consequence_and_essential_incompleteness_v46.pdf) |
| LaTeX entry point | [manuscript/latex/main.tex](manuscript/latex/main.tex) |
| All LaTeX sources | [manuscript/latex/](manuscript/latex/) |
| Complete source ZIP | [logical_consequence_v46_source.zip](manuscript/logical_consequence_v46_source.zip) |
| Earlier manuscripts and source packages | [manuscript/archive/](manuscript/archive/) |
| WSL2 Codex instructions | [docs/CODEX_WSL2_V46.txt](docs/CODEX_WSL2_V46.txt) |

The paper proves the comparison theorem for lifted partial conditionals and
applies it to internally generated sentence theories. It develops the syntactic
and numerical realizations, soundness and arithmetic applications, and the
Miller-sequence and three-point-cosheaf examples. All four appendices are part
of the PDF and the modular source tree.

The source directory is `manuscript/latex/`. Its `main.tex` assembles the
sections and appendices. The source ZIP extracts to `latex/`. Earlier PDFs,
standalone TeX files, source ZIPs, and reference manuscripts are kept in
`manuscript/archive/`; their file contents are preserved. The
[archive index](manuscript/archive/INDEX.json) records their former locations
and Git blob hashes.

## Lean status

The existing Lean development covers the version-5 statements recorded in
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md). That completed baseline
is retained for reuse. It does **not** establish verification of version 46.

The v46 results and remaining obligations are recorded separately in
[FORMALIZATION_STATUS_V46.md](FORMALIZATION_STATUS_V46.md). The Section 3 comparison
accepts arbitrary disjoint target idempotents and partial lifts. The subsequent
development constructs the extension to the restriction splitting and proves
regular-image foundations, with concrete syntactic and cosheaf applications.
The table distinguishes categorical syntax interfaces from their concrete
realizations; the latter require additional work.

The existing verifier builds the combined Lean entry point, checks imported
source and dependency pins, checks the preserved manuscript baseline, runs
`V5StatementAudit.lean` and `V46StatementAudit.lean`, and inspects the transitive
axioms of its retained declarations and every declaration in the v46 production
modules. It also pins the v46 TeX, PDF and source archive separately from the
historical manuscript sources. The permitted axioms are `propext`, `Quot.sound`, and
`Classical.choice`. A successful baseline verification must not be reported
as completion of v46.

## Clone or use the existing checkout

For a new checkout, use GitHub SSH authentication:

```bash
git clone git@github.com:flengyel/CategoricalEssentialIncompleteness.git
cd CategoricalEssentialIncompleteness
```

For an existing checkout, inspect `git status --short --branch` and
`git remote -v` before updating. Preserve local changes and use the existing
repository. Run the commands below in Debian or another Linux environment,
including WSL2.

## Build and verify Lean

Git, Python 3.9 or later, and Elan are required. The Lake project is in `Lean/`.
Its toolchain and complete dependency manifest are pinned; do not change
Elan's global default or copy another project's compiled files.

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Foundation | `01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d` |

For an already prepared checkout, run from the repository root:

```bash
bash scripts/verify-wsl.sh
```

For initial setup, `bash scripts/setup-wsl.sh` installs the pinned toolchain,
obtains its Mathlib cache, and invokes verification once. The verification
wrapper takes a project build lock, sets `LEAN_NUM_THREADS=1`, and preserves
the starting commit, Git status, exit status, logs and machine-readable result
in a fresh ignored `.codex-work/verify-*` directory. The underlying verifier
remains `python3 scripts/verify.py` and writes to `build-logs/`.
Run one heavy verification process at a time across projects. WSL2 does not need the hosted
executable-path adapter described in [HOST_BUILD.md](HOST_BUILD.md).

## Build the manuscript

With `latexmk` and the required TeX packages installed, run from the repository
root:

```bash
cd manuscript/latex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

This produces `manuscript/latex/main.pdf`. The versioned publication PDF remains
in `manuscript/`. The [LaTeX guide](manuscript/latex/README.md) lists the source
files; the source ZIP contains all sections, appendices, and bibliography.

## Provenance and license

[SOURCE_PINS.json](SOURCE_PINS.json) records the imported Lean sources;
[LOCAL_PATCHES.json](LOCAL_PATCHES.json) records their permitted changes.
[MANUSCRIPT_SOURCE.json](MANUSCRIPT_SOURCE.json) distinguishes the current
manuscript target from the retained v5 verification baseline. The v46 manuscript
was published at `558a20eed4c62d59eada05f5500cf233671078e9`; the directory
reorganization changes no mathematical text or Lean source.

The software uses the existing [Apache-2.0 license](LICENSE). Manuscript terms
are specified in [manuscript/NOTICE.md](manuscript/NOTICE.md).
