# Domains, finite proofs, and essential incompleteness

The current note is [Domains, finite proofs, and essential incompleteness](domains_hoare_profunctors_essential_incompleteness.pdf)
([LaTeX source](domains_hoare_profunctors_essential_incompleteness.tex),
29 October 2026, 23 pages).

The note proves a Turing-morphism inseparability theorem under explicit
binary-case hypotheses, constructs finite-proof initial algebras in the
numerical restriction-idempotent splitting, and defines the functor taking
proof-conclusion maps to their ranges. Trace-to-proof maps connect these
constructions in a consistent c.e. essentially incomplete propositional theory.
Hoare profunctors, weakest liberal preconditions, polynomial bicomodules, and
conditional arithmetic applications are developed separately. Section 13
states the remaining existence problem for general recursion categories.
The unused appendices have been removed.

Build the self-contained source from this directory with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error domains_hoare_profunctors_essential_incompleteness.tex
```

The [outline and review records](../Audit/2026-10-29-polynomial-proofs/README.md)
include the mathematical and writing reviews, compilation status, and
source/PDF hashes. This note has not been formalized in Lean.

## Earlier notes


The note [Deduction and essential incompleteness in recursion categories](deduction_and_essential_incompleteness.pdf)
([LaTeX source](deduction_and_essential_incompleteness.tex), 29 October 2026)
constructs deductive closure from rule morphisms, ranges, and Heller's stable
unions. Theories are closed restriction domains; the representation condition
implies inseparability of their positive and negative domains and essential
incompleteness. Its arithmetic realization verifies the uniform c.e. stage
construction and includes the theorem for a possibly non-c.e. base theory.

Build this note with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error deduction_and_essential_incompleteness.tex
```

The range-and-stable-union closure construction in this note is a mathematical
development; it has not yet been added to the Lean formalization. The
[review and continuation record](../Audit/2026-10-29-deduction/README.md)
records its relation to the existing sources.

The [outline and assessment against the Di Paola--Heller program](../Audit/2026-10-29-program/README.md)
examine the connection between deductive closure, representation, and intrinsic
categorical recursion, and record the separate mathematical writing review.

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
