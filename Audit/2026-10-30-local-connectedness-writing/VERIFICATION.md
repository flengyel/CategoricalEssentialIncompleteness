# Verification of the writing revision

Baseline: `3f87a703c635c6c029f9c2bcb42aed5430ff8590`.

## Scope and rename

The active source/PDF pair is now
`manuscript/local_connectedness_and_essential_incompleteness.tex` and `.pdf`.
The old active filenames `syntactic_model_range_functors.tex` and `.pdf`
are removed. Active repository links and the manuscript build command use
the new basename. Historical audit reports retain the names and hashes of
the versions they actually reviewed.

The changes are an expanded introduction and literature discussion,
an abstract rewrite, early categorical preliminaries, explicit definitions
in the cosheaf application, bibliography additions, and corresponding
documentation. The model-family, lifting, arithmetic, and endpoint proofs
retain their mathematical content. The previous proof verification is
reused for unchanged arguments. Added definitions and literature claims
are covered by the new writing, source, and hostile-referee reports.

The committed baseline PDF was checked against its Git blob
`44aeca227495f6213c63defd2786b54c5d9eba92`; it did contain an Introduction.
This does not identify the PDF the author was viewing. The confirmed
defects were the thin literature discussion and the unexplained terminology,
which the present revision addresses directly.

## Build and document checks

From `manuscript/`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../build/local-connectedness \
  local_connectedness_and_essential_incompleteness.tex
```

- Build succeeded: **15 pages**.
- No warnings, unresolved citations/references, undefined controls, or
  overfull/underfull boxes occur in the final TeX log.
- All **27** explicit labels are unique; every reference resolves.
- All **13** bibliography entries are cited; every citation resolves.
- The fifteen-page contact sheet was inspected, with the opening,
  literature discussion, preliminaries, added syntax definitions, and
  concluding theorem also inspected at readable resolution.
- The abstract is on page 1, Introduction on pages 1–3, categorical
  preliminaries on pages 3–4, and the discussion excluding the primed
  systems on pages 2–3.
- The manuscript has no drafting/review commentary and does not use
  “diagonal proof,” “diagonal argument,” “Turing compiler,” or “evaluator.”
- The PDF in `manuscript/` is copied from the final build.

## Artifact identity

| File | SHA-256 |
| --- | --- |
| `manuscript/local_connectedness_and_essential_incompleteness.tex` | `1078044059fe239c27fdc82a9b69e7995e3b28c03d7310ff1ffb4164948d439f` |
| `manuscript/local_connectedness_and_essential_incompleteness.pdf` | `0e51e9b96d497c927253d90443cb00c3e0d70bfb4456d2c01170072c79dbb170` |
| `manuscript/sources/LOCOct10f.tex` | `039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab` |

The revised source Git blob is
`1bd45819d2b528c5ba1cced7eac47ffecf93c400`; the PDF Git blob is
`30a02a688006db4bd26ebb8504e258b60f4f49d1`.
LOCOct10f and earlier construction manuscripts are unchanged.
No Lean file was changed or rebuilt. The older Lean axiom audit is not
evidence for the paper proofs in this revision.

## Mathematical scope

The revision discharges no new construction hypothesis. It makes explicit
the already established model-family lifting and effective observations.
The arithmetic conclusion concerns consistent c.e. extensions of PA;
the nonnumerical conclusion concerns consistent computational extensions
represented by domains in the fixed three-point category. A broader theorem
still requires suitable effective observation functors and compatible
comparisons when presentations change. Arbitrary external theories and
arbitrary recursion categories are not covered.
