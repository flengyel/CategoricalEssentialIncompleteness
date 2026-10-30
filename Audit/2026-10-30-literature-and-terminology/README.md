# Version 3: terminology, exposition, and literature

30 October 2026.

The [Version 3 manuscript](../../manuscript/essential_incompleteness_via_local_connectedness_v3.pdf)
([source](../../manuscript/essential_incompleteness_via_local_connectedness_v3.tex))
uses restriction idempotents throughout its categorical exposition. The
abstract states the categorical inseparability theorem first and identifies
arithmetic essential incompleteness separately as a logical consequence.
The full-source economy pass removes the discussion of unused Heller
hypotheses and other irrelevant or repeated disclaimers. The theorem
hypotheses and substantive counterexamples remain.

- [Terminology and prose review](TERMINOLOGY_REVIEW.md): actual outline,
  changes, disclaimer decisions, and every remaining occurrence of
  “domain,” including unchanged internal labels and actual domains of definition.
- [Literature comparison](LITERATURE_COMPARISON.md): Di Paola–Heller,
  Bernardi, Heller, Cockett–Hofstra and related work, with primary sources
  and explicit access limits. Cockett's attribution is to the present
  author, Florian Lengyel. No independent use of the local-connectedness
  method for recursive inseparability was located.
- [Delivery metadata](DELIVERY.json): source and PDF SHA-256 hashes.
- [Version 2 reviews](../2026-10-29-introduction-economy/README.md): the
  earlier mathematical review and proof-dependency record.

The terminology editor read the complete source, and a second reader
independently checked the complete source for irrelevant disclaimers.
The coordinating editor reviewed the changes. All 49 labels, 11 bibliography
keys, and 88 mathematical displays are unchanged. One repeated Heller
citation was removed with its paragraph; no bibliography entries were added.
The literature comparison is separate from the manuscript.

The exact delivered source was compiled with:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=../build/version3 essential_incompleteness_via_local_connectedness_v3.tex
```

The final PDF has 28 pages. The final log contains no warnings, undefined
references, or overfull/underfull boxes. All pages were inspected in an
overview; pages 1–3, 8, 10–11, and 16 were inspected at readable scale.
These checks cover the revised exposition and layout. The mathematical
arguments were not independently re-audited in full during this terminology
revision. No Lean sources changed or Lean checks were run.
