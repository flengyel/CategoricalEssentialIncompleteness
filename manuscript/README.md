# Manuscript version 46

**Logical consequence and essential incompleteness in recursion categories**,
2 November 2026.

| Item | Location |
| --- | --- |
| PDF | [logical_consequence_and_essential_incompleteness_v46.pdf](logical_consequence_and_essential_incompleteness_v46.pdf) |
| LaTeX entry point | [latex/main.tex](latex/main.tex) |
| Source directory and guide | [latex/](latex/) |
| Complete source ZIP | [logical_consequence_v46_source.zip](logical_consequence_v46_source.zip) |
| Older manuscripts and source packages | [archive/](archive/) |

The PDF includes all four appendices. The source ZIP extracts to `latex/` and
contains the same 22 TeX files as the source directory, plus its README.

From the repository root, build with:

```bash
cd manuscript/latex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The output is `main.pdf`. Earlier PDFs, standalone TeX sources, source ZIPs,
and reference manuscripts have moved to `archive/` with their contents unchanged.
See its [index](archive/INDEX.json) for the old and new paths and blob hashes.

The [Lean status](../FORMALIZATION_STATUS.md) records the completed v5 baseline.
The [v46 Codex instructions](../docs/CODEX_WSL2_V46.txt) govern new work;
v46 is not yet certified by the existing v5 statement audit.

See [NOTICE.md](NOTICE.md) for manuscript licensing.
