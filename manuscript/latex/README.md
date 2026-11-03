# LaTeX sources — version 46

**Logical consequence and essential incompleteness in recursion categories**,
2 November 2026.

[Publication PDF](../logical_consequence_and_essential_incompleteness_v46.pdf) ·
[Complete source ZIP](../logical_consequence_v46_source.zip) ·
[Older manuscripts](../archive/)

`main.tex` assembles the paper. Follow its input order; source filename numbers
do not necessarily match the printed section numbers. All four appendices and
the bibliography are included. This directory is named `latex/` in both the
repository and the source ZIP.

## Build

Run from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The output is `main.pdf`. The versioned publication PDF is retained one
directory above. Changing the directory name does not change any TeX content.

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

## Revisions

Publish mathematical or prose revisions under a new version number, preserving
the previous release in `manuscript/archive/`. Keep the current PDF, source ZIP,
and source guide synchronized. The directory reorganization preserves v46.
