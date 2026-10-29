# Verification: general construction supplement

Date: 29 October 2026.

## Final artifacts

| Artifact | SHA-256 |
| --- | --- |
| `manuscript/general_recursion_category_construction.tex` | `3baa04a2cc03c2e1b50721aa9489b3687e6d7db1547f58c21cb618bbb99b3491` |
| `manuscript/general_recursion_category_construction.pdf` | `f1dd251da1eff19f921f8c0d49489a2c6e24f0c96d0363542d00bfc450f6c550` |

The PDF has 13 pages and is compiled from the recorded self-contained source.

## Checks performed

- `latexmk -pdf -interaction=nonstopmode -halt-on-error general_recursion_category_construction.tex` completed with exit status 0.
- The final TeX log contains no warnings, undefined references, or overfull or
  underfull boxes.
- All 13 pages were rendered with Poppler. The primary agent inspected the
  complete set of contact sheets; the writing reviewer inspected the final
  rendered pages. No clipped displays or overlapping text were found.
- The hostile mathematical review checked finite-stage initiality, typed
  coding, parameterized recursion, the range filter, total-parameter strength,
  numerical realization, consistency, and the essential-extension argument.
- The mathematical-writing review checked the complete source against the
  governing writing source and applied definitions-before-use and explicit
  functor-typing requirements. Confirmed editorial defects were resolved.
- Heller's §10, Example 5, printed p.1267, was checked directly in the supplied
  1990 paper. Garner–Lin's selected class and subobject comparison were checked
  in §3.1 and Lemma 9 of the primary source.
- Following the warning about Heller's typos, printed pp.1261–1262 and 1267
  were inspected as page images. The targeted source check distinguishes
  printed typing errors from OCR corruption and records their effect on this
  supplement. It is not a complete errata list or a verification of every
  result in Heller's paper.

The review records identify conditional hypotheses and remaining construction
questions. They are mathematical reviews, not machine-checked proofs or a
certification of novelty. No Lean files changed and no Lean verification was
run for these new statements.
