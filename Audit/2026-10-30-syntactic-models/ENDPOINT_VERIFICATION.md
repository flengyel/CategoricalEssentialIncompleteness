# Introduction and endpoint-construction verification

Baseline: faf3d070c94681748b6cb99d22243173bd665644.

## Mathematical changes

The revised title and abstract state essential incompleteness. The new
Introduction follows LOCOct10f's motivation and explains the Di Paola–Heller
program, target local connectedness, the precise range-functor lifting
hypothesis, and the effective proof-observation step.

The arithmetic section now explicitly derives numerical inseparability
from the local-connectedness theorem applied to Rec→Pfn. This gives an
actual dependency of the arithmetic essential-incompleteness proof on the
stated theorem; internal inseparability in S_T alone is not substituted
for the separate effective step.

The new three-point construction includes:

- Covariant evaluation on partial spans, with identity/composition and
  the asserted structural preservation.
- Endpoint preservation of the displayed Turing morphism, using total
  parameter specialization.
- A counterexample showing failure of central Turing universality.
- Categorical endpoint probes and their numerical presentations.
- Atomic proof inclusions and c.e. observed pairs on N².
- A covariant extension functor and the proof-search contradiction.
- The restriction-equivalence argument establishing the source is
  nonnumerical.

The endpoint pair in the finite-proof presentation uses singleton output
domains; its numerical inseparability is proved by the explicit endpoint
Turing morphism. It is not identified with the summand-output pair of
the general local-connectedness theorem. Both applications are stated
with their actual hypotheses.

Confirmed typing and exposition issues were resolved: a global point
contributes its range; the probe functor has target Pfn with an explicit
effective presentation; domain idempotents and their carriers have
distinct notation; syntax initiality is in the total diagram category;
and the source poset of the extension functor is explicit.

The mathematical and writing checks are author-side reviews recorded in
ENDPOINT_HOSTILE_REVIEW.md and ENDPOINT_WRITING_REVIEW.md.

## Build and rendering

From manuscript/:

~~~bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../build/syntactic-models syntactic_model_range_functors.tex
~~~

The final PDF has twelve pages. The final log has no warnings, unresolved
references or citations, undefined controls, or overfull/underfull boxes.
All 26 explicit labels are unique; all references and citations resolve.

The twelve-page contact sheet was inspected. The introduction, arithmetic
proof, endpoint definitions, and extension theorem were also inspected at
readable resolution, including the final title/abstract and the
nonnumerical-equivalence argument. The manuscript contains no drafting or
review commentary. The PDF in manuscript/ is copied from the final build.

| File | SHA-256 |
| --- | --- |
| manuscript/syntactic_model_range_functors.tex | 780dec35305daf617191f5dff0f216d89ca0e7b81dccd7e9888180c29a2455e4 |
| manuscript/syntactic_model_range_functors.pdf | 05db3881fc52ee29ea53aa2b89570dad3d9c1fd540b16b8cfedea791f329e3f5 |
| manuscript/sources/LOCOct10f.tex | 039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab |

Earlier construction sources, the archived LOCOct10f source, and all Lean
files remain unchanged. Their existing verification is reused. No result
in this continuation is claimed to have been formalized in Lean, and the
older Lean audit was not run as a substitute for these paper proofs.

## Remaining construction

The three-point effective observation and fixed-presentation extension
comparison are supplied. Extending them to a broader class requires
effective observations preserving the specified pair and atomic
inclusions, together with compatible maps when presentations change.
No construction for arbitrary external theories or arbitrary recursion
categories is asserted.
