# Version 9: terminology and typing revisions

The manuscript is [Local connectedness in recursion categories and essential incompleteness](../../manuscript/essential_incompleteness_via_local_connectedness_v9.pdf)
([source](../../manuscript/essential_incompleteness_via_local_connectedness_v9.tex)), 31 October 2026.

## Changes

- The Miller construction uses explicitly defined binary representations. References to a “row” have been replaced by the indexed subsequence in question. Its citation to Miller's 2004 construction is retained.
- Restriction idempotents are distinguished from the sets on which they are partial identities. Undefined uses of “support” are removed.
- The objects of the syntactic category are closed terms with syntactic equality. Their assigned sets, numerical codings, PA formulas, and model interpretations are specified separately. An explicit functor compares this presentation with Montagna's set-object presentation.
- Program indices, partial functions, proof codes, derivation trees, algebra carriers, and algebra structures are distinguished. The carrier functor is written `J_rec` to distinguish it from the fork category `J`.
- The numerical codes for finite sequences are declared before use. The domain of each induced partial map uses the source object's encoding.
- The abstract and introduction state the categorical theorem and Miller application directly.

The author's range-functor definition, including preservation of restrictions,
ranges, restriction zeros, and binary restriction coproducts, is unchanged.
The statements labeled `thm:local-lifting`, `prop:disjoint-joins`, and
`cor:domain-incompleteness` are byte-identical to version 8. No separate
hypotheses have been added for properties already included in that definition.

## Reviews

The [prose review](PROSE_REVIEW.md) records the actual outline, full-source
reading, final corrections, and limits of the check. It applies the
Mathematical Writing workflow and Knuth, Larrabee, and Roberts's
[Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
with Heller's exposition as a model. The governing checks include defining
notation before use, keeping its meaning consistent, supplying the types
needed to read an equation, and writing complete mathematical sentences.

The [hostile mathematical review](MATHEMATICAL_REVIEW.md) checks the changed
definitions and equations against their immediate dependencies. Its findings
have been resolved in the published source. This was a review of the changes,
not a new proof of every result or a Lean audit. Montagna's standard
arithmetization results remain cited dependencies.

## Verification

- `latexmk -pdf -interaction=nonstopmode -halt-on-error` completed successfully.
- The PDF has 39 pages. The final log contains no warnings, overfull or
  underfull boxes, or undefined-reference messages.
- All pages were rendered and inspected in contact sheets. The revised
  sequence-coding passages were also inspected at a larger scale.
- All version 8 labels and bibliography keys are retained. A source scan
  found no prose occurrence of “row,” “support,” or “supported”; `row sep`
  occurs only as a TikZ layout option.
- The unchanged definition and three statements were checked by direct
  source comparison. No Lean files were changed or tests run. The Lean
  development remains indexed to version 5; version 9 has not been
  reconciled with it.

SHA-256:

| File | Digest |
|---|---|
| v9 TeX | `c71c7a10ba6df6f3c9657a71e7808417d0ce3330c99dede337e89e3668cc4831` |
| v9 PDF | `0381860dcc7fbfaa2ea618da82c97f0b68410ab544302e28b27b8b685abc6909` |
