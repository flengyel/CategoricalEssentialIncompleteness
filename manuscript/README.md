# Definability and incompleteness in recursion categories

The companion note [Definability over a recursion category](definability_indexed_predicates.pdf)
([LaTeX source](definability_indexed_predicates.tex), 29 October 2026) gives the
ordinary categorical argument using indexed predicate lattices, an embedding of
computational domains, substitution, and existential representation. It proves
inseparability and incompleteness of represented extensions directly, without an
enrichment hypothesis or a Boolean quotient presentation. Its elementary
numerical example uses powersets; the existing Lean numerical model instead
uses PER subobject lattices. See the [scope and source comparison](../Audit/2026-10-29-indexed-predicates/README.md).

Version 16 states an incompleteness theorem for the definability algebras of
Definition 2.1. The proof uses their restriction, predicate, and representation
structure. The Lean development proves this supporting implication under
weaker hypotheses; assembling the full compatible definability-algebra instance
and its arithmetic Boolean presentation remains unfinished. See the
[formalization requirements](../FORMALIZATION_REQUIREMENTS.md).

The [LaTeX source](definability_comparison_v16.tex) incorporates editorial revisions
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
