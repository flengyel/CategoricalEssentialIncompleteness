# Local connectedness in recursion categories and essential incompleteness

This is the working source for version 12. The modular manuscript was
created from the [single-file version 9](../essential_incompleteness_via_local_connectedness_v9.tex).
The [version 12 PDF](../essential_incompleteness_via_local_connectedness_v12.pdf)
records this revision.

## Build

Run from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The output is [main.pdf](main.pdf). `main.tex` assembles the document with
`\input`, so file boundaries do not introduce page breaks. The appendix
numbering command remains in `main.tex`.

## Files

| File | Contents |
|---|---|
| [main.tex](main.tex) | Document assembly and section order |
| [preamble.tex](preamble.tex) | Packages, theorem environments, macros, title, author, and date |
| [abstract.tex](abstract.tex) | Abstract |
| [sections/01-introduction.tex](sections/01-introduction.tex) | Introduction |
| [sections/02-categorical-preliminaries.tex](sections/02-categorical-preliminaries.tex) | Categorical preliminaries |
| [sections/03-sections-and-inseparability.tex](sections/03-sections-and-inseparability.tex) | Sections of partial monomorphisms and inseparability |
| [sections/04-miller-sequences.tex](sections/04-miller-sequences.tex) | Miller sequences and essential incompleteness |
| [sections/05-syntactic-recursion-category.tex](sections/05-syntactic-recursion-category.tex) | The syntactic recursion category |
| [sections/06-interpretation-in-models.tex](sections/06-interpretation-in-models.tex) | Interpretation in models |
| [sections/07-faithful-family-and-theory-extension.tex](sections/07-faithful-family-and-theory-extension.tex) | A faithful family and theory extension |
| [sections/08-essential-incompleteness-of-arithmetic.tex](sections/08-essential-incompleteness-of-arithmetic.tex) | Essential incompleteness of arithmetic |
| [sections/09-three-point-space.tex](sections/09-three-point-space.tex) | A recursion category from a three-point space |
| [appendices/a-three-point-cosheaves.tex](appendices/a-three-point-cosheaves.tex) | Appendix: The three-point cosheaf construction |
| [appendices/b-finite-syntax-and-proofs.tex](appendices/b-finite-syntax-and-proofs.tex) | Appendix: Finite syntax and proofs |
| [appendices/c-section-lifting.tex](appendices/c-section-lifting.tex) | Appendix: Necessity of section lifting for inseparability |
| [bibliography.tex](bibliography.tex) | References |

## Section-by-section revision

Use “morphism” throughout the mathematical prose.

Increment the manuscript version for each published revision. Update the
title page and current-version links, and retain a PDF with the version in
its filename.

Work on the requested file, consulting definitions and results elsewhere
when the argument requires them. Keep observations about other sections
separate from edits to the selected section. Compile the assembled document
to check references and layout after changes. A review of one section does
not establish the correctness of the complete paper.

The [outline and abstract review for version 12](../../Audit/2026-10-31-outline-v12/README.md)
records the section functions, theorem dependencies, source-based writing review,
and abstract revision.
The abstract is accepted. The next section is the introduction; use the
[continuation prompt](../../CONTINUATION_INTRODUCTION_REVIEW.md) and
[theorem and proof synopsis](../../notes/manuscript_v12_theorems_and_proofs.md).
The Lean formalization remains indexed to version 5.
