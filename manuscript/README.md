# Definability and incompleteness in recursion categories

Version 16 proves categorical essential incompleteness. The
[LaTeX source](definability_comparison_v16.tex) incorporates editorial revisions
dated 28 October 2026, and the [PDF](definability_comparison_v16.pdf) is rebuilt
from that source. The original provenance is retained in
[MANUSCRIPT_SOURCE.json](../MANUSCRIPT_SOURCE.json); the revised hashes are in
[LOCAL_PATCHES.json](../LOCAL_PATCHES.json).

The LaTeX file is self-contained. With a TeX installation that provides its
listed packages, rebuild the PDF from this directory with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error definability_comparison_v16.tex
```

See [NOTICE.md](NOTICE.md) for the manuscript licensing scope.
