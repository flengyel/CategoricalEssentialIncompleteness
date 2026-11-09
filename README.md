# Logical consequence and essential incompleteness in recursion categories

Gödel’s arithmetization represents formulas and finite proofs by numbers and
their effective operations and relations within arithmetic. We begin with
computation, axiomatized by recursion categories, and construct
propositional and first-order deductive systems in the restriction
idempotent completions of these categories. We prove a categorical form of
essential incompleteness for the generated internal theories, realizing Di
Paola and Heller’s objective of obtaining generalized incompleteness from
categorical recursion theory. In the completion of the syntactic recursion
category for Peano arithmetic, we represent computably enumerable extensions
of Peano arithmetic by internal theories. For each consistent extension, a
categorical comparison theorem proves incompleteness of both the internal
theory and the arithmetic extension, and gives an independent sentence
uniformly from an index for the extension’s axiom enumeration. A realization
based on a Miller sequence gives a consistent theory of real closed fields
expanded by constants naming the sequence. Every consistent extension is
incomplete if one oracle program semidecides its axioms using any binary
representation of the sequence. A realization using cosheaves on a
three-point space gives two consistent propositional theories whose
consistent computably enumerable extensions in the same language are
incomplete.

The current manuscript and Lean formalization target are **version 51**,
dated 9 November 2026.

| Item | Location |
| --- | --- |
| Current PDF | [logical_consequence_and_essential_incompleteness_v51.pdf](manuscript/logical_consequence_and_essential_incompleteness_v51.pdf) |
| LaTeX entry point | [manuscript/latex/main.tex](manuscript/latex/main.tex) |
| All LaTeX sources | [manuscript/latex/](manuscript/latex/) |
| Complete source ZIP | [logical_consequence_v51_source.zip](manuscript/logical_consequence_v51_source.zip) |
| Earlier manuscripts and source packages | [manuscript/archive/](manuscript/archive/) |
| Palomar abstract | [docs/PALOMAR_ABSTRACT.txt](docs/PALOMAR_ABSTRACT.txt) |
| WSL2 Codex instructions | [docs/CODEX_WSL2_CURRENT.txt](docs/CODEX_WSL2_CURRENT.txt) |

The source directory is `manuscript/latex/`. Its `main.tex` assembles the
sections and appendices. The source ZIP extracts to `latex/`. Earlier PDFs,
standalone TeX files, source ZIPs, and reference manuscripts are kept in
`manuscript/archive/`; their file contents are preserved. The
[archive index](manuscript/archive/INDEX.json) records their former locations
and Git blob hashes.

## Lean status

The current correspondence table is
[FORMALIZATION_STATUS_V51.md](FORMALIZATION_STATUS_V51.md). It records all 62
numbered results and three definitions and their Lean declarations. The earlier [v5 table](FORMALIZATION_STATUS.md) records the
retained baseline.

All 62 numbered results have proofs. The [continuation report](docs/V46_SYNTAX_CONTINUATION_2026-11-05.md) records the completed constructions and the successful integrated v48 verification at proof commit `d437827275d64f6500e6a3bca2ee318420d11edd`. Version 51 updates the approved abstract; the introduction, definitions, theorem statements, and proofs are unchanged. The [v51 abstract update](docs/V51_ABSTRACT_UPDATE_2026-11-09.md) records the changes and manuscript checks. The [Palomar editorial report](docs/PALOMAR_EDITORIAL_REVIEW_2026-11-09.md) records the subsequent source port and package preparation, whose verification is in progress.

Lean verification follows the current manuscript. Every manuscript revision
must update `MANUSCRIPT_CURRENT.json`, the correspondence table, source archive,
PDF, and any affected statement checks in the same commit. The verifier checks
the version and bytes of the active sources, checks the archive against those
sources, builds the combined Lean entry point, runs `CurrentStatementAudit.lean`,
and inspects transitive axioms through `CurrentAxiomAudit.lean`. It also checks
imported source and dependency pins and the retained baseline. The permitted
axioms are `propext`, `Quot.sound`, and `Classical.choice`.

The existing `V46` Lean module and namespace names identify implementations.
The active manuscript target is selected by `MANUSCRIPT_CURRENT.json`.

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
[MANUSCRIPT_SOURCE.json](MANUSCRIPT_SOURCE.json) records the earlier
manuscript baseline. [MANUSCRIPT_CURRENT.json](MANUSCRIPT_CURRENT.json) records
the current verification target, its source hashes, PDF, and source archive.

The software uses the existing [Apache-2.0 license](LICENSE). Manuscript terms
are specified in [manuscript/NOTICE.md](manuscript/NOTICE.md).
