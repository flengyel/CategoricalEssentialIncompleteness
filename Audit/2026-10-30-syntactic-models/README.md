# Local connectedness, range functors, and essential incompleteness

The note [Local connectedness, range functors, and essential incompleteness](../../manuscript/archive/essential_incompleteness_via_local_connectedness.pdf)
([source](../../manuscript/archive/essential_incompleteness_via_local_connectedness.tex),
29 October 2026, 26 pages) constructs
a faithful range functor from S_T to a locally connected target, proves
the lifting hypothesis, and records compatibility with extensions.
Its introduction develops the relevant literature and explains the passage
from computational inseparability to essential incompleteness.
The endpoint continuation constructs an actual observation functor from
the three-point category to the split classical recursion category.

S_T itself is not locally connected for consistent c.e. extensions of PA.
This is Di Paola–Montagna Corollary 4.4. The note explicitly distinguishes
that source from the product target. Section 6 proves the local-connectedness
inseparability theorem and a sufficient lifting criterion, retaining the
lifting hypothesis in the theorem statement.
The current introduction includes Rosolini's partial-map framework, Heller's
local-connectedness theorem, Lengyel2004 with the version-10 corrections,
and Bernardi's related method. Partial-map and restriction definitions
precede the constructions. The pointwise systems S'_T of Di Paola–Montagna
are excluded using Lengyel's composition-failure result; the valid uniform
quotients S_T remain the source categories.

Appendix A proves the diagram-category structure, frames, Turing universality,
and restriction-splitting equivalence. Appendix B supplies the finite syntax
and proof construction and its consistency proof. Appendix C gives a
counterexample only to the statement with the lifting hypothesis omitted.
The paper includes the proofs needed for its introductory claims and has no
bibliographic dependency on LOCOct10f or the companion cosheaf note.

The [current self-contained version's review and verification record](../2026-10-29-self-contained-local-connectedness/README.md)
covers these proofs and appendices. The
[earlier writing record](../2026-10-30-local-connectedness-writing/README.md)
and the records below retain the filenames and hashes of the versions they
checked.

- [Revised outline and hypotheses](ENDPOINT_OUTLINE.md)
- [Source check](SOURCE_CHECK.md)
- [Endpoint author-side mathematical review](ENDPOINT_HOSTILE_REVIEW.md)
- [Revised mathematical-writing review](ENDPOINT_WRITING_REVIEW.md)
- [Endpoint-version verification](ENDPOINT_VERIFICATION.md)

The original eight-page version remains documented by its
[outline](OUTLINE.md), [hostile review](HOSTILE_REVIEW.md),
[writing review](WRITING_REVIEW.md), and [verification](VERIFICATION.md).
Those records describe the base commit, not the subsequent additions.

The reviews are author-side checks, not independent peer review.
No new theorem has been formalized in Lean. Previously verified,
unchanged manuscripts and the older Lean development were not rebuilt.

The endpoint construction supplies intrinsic probes, effective domain
observations, and a covariant extension functor into Pair(Rec).
The remaining problem is to identify broader classes of effective
observation functors and compatible comparisons when the presentation
changes. Neither arbitrary recursion categories nor arbitrary external
theory presentations are covered.
