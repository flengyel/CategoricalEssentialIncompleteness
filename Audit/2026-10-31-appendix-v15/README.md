# Appendix clarification and versioned files

Version 15, 31 October 2026.

The standalone appendix now proves why its chosen copairings define Boolean
operations under the stated categorical hypotheses. Pullback stability
decomposes `(1+1) × (1+1)` into four copies of the terminal object. The specified
summand morphisms determine conjunction and disjunction through that
decomposition. The Boolean laws are equations of morphisms, checked using the
jointly epimorphic injections into the finite powers of `1+1`.

A separate agent checked the new paragraph and both complement equations.
The argument needs no generator assumption on the terminal object. The
construction is not a claim about an arbitrary coproduct, nor does it assert
that `1+1` is a subobject classifier.

The version 14 source retrieved from both GitHub and the saved file already
had the corrected copairings. Unversioned standalone download paths nevertheless
left stale displays indistinguishable. Every current downloadable artifact
now has a versioned filename, and the PDFs visibly identify version 15.

## Files

- [Standalone appendix PDF](../../manuscript/first_order_syntax_and_deductive_closure_appendix_v15.pdf)
  and [LaTeX source](../../manuscript/first_order_syntax_and_deductive_closure_appendix_v15.tex).
- [Version 15 manuscript](../../manuscript/essential_incompleteness_via_local_connectedness_v15.pdf)
  and [source archive](../../manuscript/local_connectedness_v15_source.zip).
- [Version 15 review](appendix_a_review_v15.pdf) and
  [review source](appendix_a_review_v15.tex).

The [version 14 four-agent reports](../2026-10-31-appendix-v14/README.md)
remain separate records. They are not represented as fresh full reviews of
version 15. The section order, labels, bibliography, and previously implemented
corrections are unchanged. The accepted abstract and other mathematical sections
are unchanged. The source guide now requires versioned names for every exported
file on each revision.

## Verification

The standalone appendix (8 pages), review (2 pages), and assembled manuscript
(46 pages) compile without LaTeX warnings, unresolved references or citations,
or overfull/underfull boxes. The revised pages and page transitions were visually
inspected. The standalone and integrated mathematical bodies agree after
excluding the standalone version label and the integrated compatibility label.

The mathematical check was confined to the added Boolean-algebra argument.
No fresh full-manuscript, bibliographic, novelty, or Lean verification is claimed.
