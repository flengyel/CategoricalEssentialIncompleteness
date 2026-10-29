# Source check and verification

Date: 29 October 2026. Repository baseline:
e98536008177001780499378f4752e99b2e3d00e.

## Primary source

Sridhar Ramesh, *Introspective Theories and Geminal Categories* (2023),
[Berkeley thesis](https://escholarship.org/uc/item/3mn0c475).
The primary PDF was consulted at these printed-page locations:

| Location | Use |
| --- | --- |
| pp.31–34, Definition 1.51, Corollary 1.55, Theorem 1.56 | Arithmetic left comma-stability and initiality among lex functors; the note reconstructs the comma application |
| pp.34–35, Theorem 1.63 and Observation 1.66 | Initial internal models of finitely axiomatized lex theories, preservation, and the AU theory |
| p.42, Theorem 1.80 and following paragraph | External global sections are arithmetic; this assertion does not internalize |
| pp.45–48, Definitions 2.1–2.2 and Theorem 2.5 | Introspection and the equivalent S,N data |
| pp.63–65, Definition 3.2 | Distinct modal endofunctors on base and internal global category |
| pp.82–83, Theorem 4.19 and Corollary 4.21 | Löb on the relevant categories; imported, not re-proved here |
| pp.115–118, §6.2–6.3 | Initiality-based and initial-model constructions |
| p.120, Construction 6.11 and Observation 6.12 | Internal AU construction and canonical initial example |
| pp.120–123, Construction 6.13 and Observation 6.15 | Localization condition and inclusion of unsound theory examples; these constrain the remaining extension problem |

The new note's elementary deductions are checked separately from these
imported results. In particular, the exact identity between global points
of the internal hom and external arrows replaces any proposed soundness
assumption. The initial-example equivalence is not extended to arbitrary
internal theories. No novelty claim is based on the source search.

## Build

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error intrinsic_introspection_and_extensions.tex
```

Final result: success, three pages; no warnings, unresolved references,
overfull boxes, or underfull boxes. All final pages were rendered at 120 dpi
with pdftoppm and visually inspected. A missing display delimiter in the
first draft was corrected before the successful build.

| Artifact | SHA-256 |
| --- | --- |
| intrinsic_introspection_and_extensions.tex | fd1fa532c8cd31c3ba8bc0446f9c063fd882fba07ea0a4e203814c62431d3edd |
| intrinsic_introspection_and_extensions.pdf | 391c284629b26957757a48271c0a2d613c45642b74fc86b1472c96af1be80091 |

Only this new source/PDF, its audit directory, and the three navigation
documents are included in the publication tree. Earlier mathematical
sources and PDFs are preserved by their baseline blobs; their verification
is reused. Publication uses an expected-head update of main without force,
and an exact changed-path comparison. No Lean files were changed or run.
