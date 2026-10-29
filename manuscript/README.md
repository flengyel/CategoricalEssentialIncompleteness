# Domains, finite proofs, and essential incompleteness

## Computational constructions

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

## General construction

The supplement [Finite proof algebras in range restriction categories](general_recursion_category_construction.pdf)
([LaTeX source](general_recursion_category_construction.tex), 29 October 2026)
proves a finite-stage initial-algebra theorem and obtains typed constructor
embeddings from universal-object dominance and universal ranges. A parameterized
recursion theorem constructs partial folds from a Turing morphism, leaving the
specified stable domain unions as existence hypotheses. Under regularity,
range/image compatibility, parameter-stable finite recursion, and decidable atom
equality, disjoint domains give a consistent classical presentation; inseparability
makes every consistent computational extension incomplete.

The numerical split category realizes the stated construction hypotheses. The
final section credits Heller's recursion-category example without ranges and
checks a particular selected presheaf completion. The [outline and reviews](../Audit/2026-10-29-general-construction/README.md)
and [continuation prompt](../CONTINUATION_GENERAL_RECURSION_CATEGORIES.md)
record the remaining general existence questions. This supplement is not yet
formalized in Lean.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error general_recursion_category_construction.tex
```

## Iteration and computational cosheaves

[Iteration domains, finite proofs, and computational cosheaves](iteration_domains_and_cosheaves.pdf)
([LaTeX source](iteration_domains_and_cosheaves.tex), 29 October 2026, 14 pages)
continues the supplement without changing its conditional results.

The note reconstructs Heller's iteration lemma using total maps of finite
trace objects. A finite worklist has the same agreement union as the
constructor stages, with separate proofs of preservation by products,
total inverse images, and finite coproducts. Weak choice, universal
product-compatible ranges, and finite limits give regularity and identify
ranges with regular images. A finite equality-constraint argument removes
decidable atom equality from consistency for these constructed proof algebras.

The example consists of computational cosheaves on the Sierpiński space:
arrows between c.e. carriers, with computational commuting squares.
It has a universal object, a parameter-universal Turing morphism, compatible
frames, and the required binary case distinction. Its universal object
lacks decidable equality, and its total category is not equivalent to
the numerical category. The final section explains why pointwise products
and formula assignments fail for general cosheaves.

~~~bash
latexmk -pdf -interaction=nonstopmode -halt-on-error iteration_domains_and_cosheaves.tex
~~~

The [review and verification record](../Audit/2026-10-29-iteration-cosheaves/README.md)
includes the Lengyel2004/errata comparison and the checked hypotheses.
These are paper proofs; no Lean files were changed.

## Range completion and the three-point space

[Range completion and computational cosheaves on a three-point space](range_completion_three_point_cosheaves.pdf)
([LaTeX source](range_completion_three_point_cosheaves.tex), 29 October 2026)
answers the range-completion question using Cockett–Guo–Hofstra's general
and discrete cartesian constructions. The latter supplies universal
agreement, but adds no total arrows on the original objects. Under
universal-object dominance, a nonfull completion therefore cannot preserve
the original evaluator's parameter-universality.

On the space with opens ∅, {c}, {a,c}, {b,c}, and {a,b,c}, computational
cosheaves are computable fork diagrams whose global values are effective
pushout quotients. The note proves regularity, ranges, extensivity, weak
choice, stable word-length coverage, universal-object dominance, frames,
and an exact-domain evaluator. It verifies binary case distinction and
applies the preceding equality-free consistency theorem. Categorical
subobjects need not induce injective maps of global pushouts; internal
products and syntax are treated accordingly.

~~~bash
latexmk -pdf -interaction=nonstopmode -halt-on-error range_completion_three_point_cosheaves.tex
~~~

The [source, review, and verification record](../Audit/2026-10-29-range-three-point/README.md)
states the remaining general completion problem. Earlier mathematical
sources are unchanged, and these new results are not Lean-formalized.

## Separate arithmetic-universe comparison

[Internal theories and intrinsic incompleteness](intrinsic_introspection_and_extensions.pdf)
([LaTeX source](intrinsic_introspection_and_extensions.tex), 29 October 2026)
starts with Ramesh's initiality construction. For an internal arithmetic
universe C in the initial arithmetic universe I, the internal hom-object
p_C=Hom_C(1,0) is unrefutable in I. It has no global element exactly when
Glob(C) is consistent. Internal arithmetic functors give coherent maps
between the modal functors and their contradiction objects. Initial models
of finitely axiomatized lex extensions supply an explicit class of these
theories and maps.

This note concerns the initial arithmetic universe. It constructs no
comparison with the given recursion category, its selected domains, or its
computational extensions. It does not advance the Di Paola–Heller
construction pursued in the preceding notes. The
[scope correction](../Audit/2026-10-29-intrinsic-introspection/SCOPE_CORRECTION.md)
records the distinction. Its mathematical review and build remain as
recorded; no result is Lean-formalized.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error intrinsic_introspection_and_extensions.tex
```

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

