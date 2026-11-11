# LaTeX sources — version 57

**Logical consequence and essential incompleteness in recursion categories**,
10 November 2026.

Companion files: `logical_consequence_and_essential_incompleteness_v57.pdf`
and `logical_consequence_v57_source.zip`.

`main.tex` assembles the paper. Follow its input order; source filename numbers
do not necessarily match the printed section numbers. All four appendices and
the bibliography are included. This directory is named `latex/` in both the
repository and the source ZIP.

## Build

Run from this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The output is `main.pdf`. The source package contains this directory as
`latex/`. Editorial review records are in the repository under `docs/reviews/`.

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
| [appendices/d-faithful-family.tex](appendices/d-faithful-family.tex) | Appendix D: Faithful model interpretations, theory extension, and provability of numeral instances |
| [bibliography.tex](bibliography.tex) | References |

## Revisions

Version 56 states the construction hypotheses in the abstract and introduction,
separates the two arithmetic theories, and distinguishes preservation of
essential incompleteness from the inseparability criterion. It specifies
the inference-algebra slice and the formula-label
membership tests in Lemma 9.6. The independent audit records all 77 proof
arguments, the 62 older Lean mappings, and the 15 open formalization
obligations.

Version 55 replaces unexplained implementation vocabulary with the finite
sequences, coproduct injections, and algebra morphisms used in the proofs.
It identifies the initial algebra used after transporting axioms and corrects
the domain reference for the inference algebra. The finite-family selector
is explicit. Numbered result labels and open Lean obligations are retained.

Version 54 revises terminology throughout the manuscript. It replaces vague
references with named objects, gives substitution codomains explicitly, and
removes empty qualifiers. Statements, hypotheses, equations, and labels are
unchanged.

Version 53 supplies the typed arithmetic Turing-parameterization calculation
and declares logical premise and conclusion morphisms before their use.
The statements and open Lean obligations are unchanged from version 52.

Version 52 adds the internal-theory adjunctions and the section on theory
extensions and recursion categories. The arithmetic, Miller, and first-order
fork constructions explicitly instantiate the general theorem. New Lean
obligations are recorded in the current correspondence table.

Version 51 replaces the abstract with the approved account of the motivation,
categorical incompleteness result, and three applications. The introduction,
definitions, hypotheses, conclusions, and proof arguments are unchanged.

Version 50 removes redundant prose, expands compressed noun phrases, and
clarifies references to mathematical objects. The approved abstract,
definitions, hypotheses, conclusions, and proof arguments are unchanged.

Version 49 uses “morphism” for categorical morphisms throughout the cosheaf
construction and the numerical and Miller arguments. The abstract, definitions,
theorem statements, hypotheses, equations and proofs are unchanged.

Version 48 updates the abstract to include arithmetic recursive inseparability
and uniform independent sentences. The introduction and all numbered results,
definitions, hypotheses, and proofs of version 47 are unchanged.

Version 57 is the current manuscript and Lean verification target.
`MANUSCRIPT_CURRENT.json` at the repository root records the active source
hashes, PDF, archive, correspondence table, and audit entry points.
Later manuscript revisions update that target in the same change.

