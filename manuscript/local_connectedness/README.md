# Logical consequence and essential incompleteness in recursion categories

Version 26, 1 November 2026.

[Manuscript PDF](../logical_consequence_and_essential_incompleteness_v26.pdf) ·
[Source archive](../logical_consequence_v26_source.zip)

Sections 3 and 4 prove the comparison theorem and its application to internally
generated sentence theories. Section 5 proves the syntactic realization.
Section 6 proves the soundness factorization for the standard code interpretation
and its ultrapowers; Section 7 applies the comparison through partial proof
search. Section 7.2 constructs one indexed family of arithmetic theories and
identifies its numeral fibers. Section 7.3 constructs a total morphism assigning
an independent sentence to every consistent standard presentation. Section 7.4
proves the numerical realization; Section 7.5 applies numerical incompleteness,
and Section 7.6 treats numeral instances and theory extension. Sections 8 and 9
contain the Miller and cosheaf applications.
The faithful model family and numeral observations are in Appendix D.
The introduction and abstract are reserved for the final revision.

The [version 26 reviews](../../Audit/2026-11-01-numerical-v26/README.md)
record the numerical realization, the computable proof-code comparisons,
and the mathematical, writing, and type checks of Sections 7.4 and 7.5.

Appendix A contains the full categorical construction of syntax, substitution,
and deductively closed theories. Its realizations are proved in the application
sections. The appendix is also available as a
[standalone PDF](../first_order_syntax_and_deductive_closure_appendix_v26.pdf)
with [LaTeX source](../first_order_syntax_and_deductive_closure_appendix_v26.tex).

## Build

Run from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The build output is `main.pdf`. The source archive contains the modular
sources, including the complete appendix and bibliography.

## Files

| File | Contents |
|---|---|
| [main.tex](main.tex) | Document assembly and section order |
| [preamble.tex](preamble.tex) | Packages, theorem environments, macros, title, author, and date |
| [abstract.tex](abstract.tex) | Abstract |
| [sections/01-introduction.tex](sections/01-introduction.tex) | Introduction |
| [sections/02-categorical-preliminaries.tex](sections/02-categorical-preliminaries.tex) | Categorical preliminaries |
| [sections/03-sections-and-inseparability.tex](sections/03-sections-and-inseparability.tex) | Diagonal comparison and lifted partial conditionals |
| [sections/03a-internal-theories.tex](sections/03a-internal-theories.tex) | Internal theories and semantic consistency |
| [sections/04-miller-sequences.tex](sections/04-miller-sequences.tex) | Miller sequences and essential incompleteness |
| [sections/05-syntactic-recursion-category.tex](sections/05-syntactic-recursion-category.tex) | The syntactic recursion category |
| [sections/05a-internal-syntax.tex](sections/05a-internal-syntax.tex) | Internal syntax, substitution, and generated theories in the total restriction splitting of S_T |
| [sections/06-interpretation-in-models.tex](sections/06-interpretation-in-models.tex) | Interpretation and soundness |
| [sections/08-essential-incompleteness-of-arithmetic.tex](sections/08-essential-incompleteness-of-arithmetic.tex) | Essential incompleteness of arithmetic |
| [sections/08a-uniform-theories.tex](sections/08a-uniform-theories.tex) | Indexed arithmetic theories and their numeral fibers |
| [sections/08b-uniform-independent-sentences.tex](sections/08b-uniform-independent-sentences.tex) | Uniform independent sentences |
| [sections/08c-numerical-realization.tex](sections/08c-numerical-realization.tex) | Numerical categories, syntax, substitution, and derivation initiality |
| [sections/08d-numerical-incompleteness.tex](sections/08d-numerical-incompleteness.tex) | Numerical application of the incompleteness theorem |
| [sections/09-three-point-space.tex](sections/09-three-point-space.tex) | A recursion category from a three-point space |
| [appendices/a-syntax-and-theories.tex](appendices/a-syntax-and-theories.tex) | Appendix A: Syntax and deductively closed theories |
| [appendices/b-three-point-cosheaves.tex](appendices/b-three-point-cosheaves.tex) | Appendix B: The three-point cosheaf construction |
| [appendices/c-section-lifting.tex](appendices/c-section-lifting.tex) | Appendix: Necessity of section lifting for inseparability |
| [appendices/d-faithful-family.tex](appendices/d-faithful-family.tex) | Appendix D: Faithful families, theory extension, and numeral observations |
| [bibliography.tex](bibliography.tex) | References |

## Publication versions

Every published revision has a new versioned PDF and source archive. The
standalone appendix has matching versioned exports. Update the displayed
PDF versions and all current download links together.

The [theorem-and-proof plan](../../Plans/comparison_soundness_paper_plan_v2.pdf)
gives the organization of the remaining revisions. The Lean formalization
remains indexed to version 5.

## Review procedure

Each revised subsection is reviewed by the hostile referee and Mathematical
Writing plugins, with an explicit type and dependency check. Correct identified
defects and repeat the reviews on the resulting text until no concrete finding
remains unresolved before proceeding to its Lean formalization.
