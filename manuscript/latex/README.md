# LaTeX sources — version 91

**Logical consequence and essential incompleteness in recursion categories**,
24 November 2026.

Companion files: `logical_consequence_and_essential_incompleteness_v91.pdf`
and `logical_consequence_v91_source.zip`.

The directory `latex/` contains the complete source. The order of the
inputs in `main.tex` is the order of the printed sections.

## Build

Run the following command in `latex/`.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The output is `main.pdf`.

## Files

| File | Contents |
|---|---|
| [main.tex](main.tex) | Document assembly and section order |
| [preamble.tex](preamble.tex) | Packages, theorem environments, macros, title, author, and date |
| [abstract.tex](abstract.tex) | Abstract |
| [sections/01-introduction.tex](sections/01-introduction.tex) | Introduction |
| [sections/02-categorical-preliminaries.tex](sections/02-categorical-preliminaries.tex) | Categorical preliminaries |
| [sections/03-sections-and-inseparability.tex](sections/03-sections-and-inseparability.tex) | Diagonal comparison and lifted partial conditionals |
| [sections/03a-internal-theories.tex](sections/03a-internal-theories.tex) | Internal theories and essential incompleteness |
| [sections/03b-internal-adjunctions.tex](sections/03b-internal-adjunctions.tex) | Generation, translations, and the free first-order adjunction |
| [sections/04-theory-extensions.tex](sections/04-theory-extensions.tex) | Associated recursion categories, theory extensions, and incompleteness transfer |
| [sections/05-syntactic-recursion-category.tex](sections/05-syntactic-recursion-category.tex) | The syntactic recursion category |
| [sections/05a-internal-syntax.tex](sections/05a-internal-syntax.tex) | Internal syntax, substitution, and generated theories in the total restriction splitting of S_T |
| [sections/06-interpretation-in-models.tex](sections/06-interpretation-in-models.tex) | Interpretation and soundness |
| [sections/08-essential-incompleteness-of-arithmetic.tex](sections/08-essential-incompleteness-of-arithmetic.tex) | Essential incompleteness of arithmetic |
| [sections/08a-uniform-theories.tex](sections/08a-uniform-theories.tex) | Indexed arithmetic theories and their numeral fibers |
| [sections/08b-uniform-independent-sentences.tex](sections/08b-uniform-independent-sentences.tex) | Uniform independent sentences |
| [sections/08c-numerical-realization.tex](sections/08c-numerical-realization.tex) | Numerical categories, syntax, substitution, and derivation initiality |
| [sections/08d-numerical-incompleteness.tex](sections/08d-numerical-incompleteness.tex) | Numerical application of the incompleteness theorem |
| [sections/04-miller-sequences.tex](sections/04-miller-sequences.tex) | Miller sequences and essential incompleteness |
| [sections/09-three-point-space.tex](sections/09-three-point-space.tex) | A recursion category from a three-point space |
| [appendices/a-syntax-and-theories.tex](appendices/a-syntax-and-theories.tex) | Appendix A: Syntax and deductively closed theories |
| [appendices/b-three-point-cosheaves.tex](appendices/b-three-point-cosheaves.tex) | Appendix B: The three-point cosheaf construction |
| [appendices/c-section-lifting.tex](appendices/c-section-lifting.tex) | Appendix C: Necessity of section lifting for inseparability |
| [appendices/d-faithful-family.tex](appendices/d-faithful-family.tex) | Appendix D: Faithful model interpretations, theory extension, and provability of numeral instances |
| [appendices/e-reading-lean-proofs.tex](appendices/e-reading-lean-proofs.tex) | Appendix E: Reading the Lean proofs |
| [bibliography.tex](bibliography.tex) | References |

The Lean links in Appendix E refer to the source of manuscript v72, tagged `cei-v72-palomar-v3`. Three theorem declarations from that source appear in [Palomar entry PALOMAR-2026-11-22-000009, version 3](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-22-000009&version=3).
