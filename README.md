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

The v46 work begins with Theorem 3.1, Corollaries 3.2 and 3.3, and Proposition
3.4, with their stated hypotheses. The [Codex instructions](docs/CODEX_WSL2_V46.txt)
specify these proofs, the subsequent dependencies, and the new correspondence
table and statement audit to implement. Those v46 checks are not yet present
in this repository snapshot.

The existing verifier builds the combined Lean entry point, checks imported
source and dependency pins, checks the preserved manuscript baseline, runs
`V5StatementAudit.lean`, and inspects the transitive axioms of its audited
declarations. The permitted axioms are `propext`, `Quot.sound`, and
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

From the repository root:

```bash
cd Lean
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
cd ..
LEAN_NUM_THREADS=1 python3 scripts/verify.py
```

The verifier writes logs and its machine-readable result to `build-logs/`.
Run one heavy verification process at a time. WSL2 does not need the hosted
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
