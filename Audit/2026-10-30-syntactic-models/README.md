# Local connectedness, range functors, and essential incompleteness

The note [Local connectedness, range functors, and essential incompleteness](../../manuscript/syntactic_model_range_functors.pdf)
([source](../../manuscript/syntactic_model_range_functors.tex)) constructs
a faithful range functor from S_T to a locally connected target, proves
the lifting hypothesis, and records compatibility with extensions.
Its introduction follows the motivation of LOCOct10f and explains the
passage from computational inseparability to essential incompleteness.
The endpoint continuation constructs an actual observation functor from
the three-point category to the split classical recursion category.

S_T itself is not locally connected for consistent c.e. extensions of PA.
This is Di Paola–Montagna Corollary 4.4. The note explicitly distinguishes
that source from the product target. It includes the necessary proofs from
the unchanged [LOCOct10f source](../../manuscript/sources/LOCOct10f.tex).

- [Revised outline and hypotheses](ENDPOINT_OUTLINE.md)
- [Source check](SOURCE_CHECK.md)
- [Endpoint author-side mathematical review](ENDPOINT_HOSTILE_REVIEW.md)
- [Revised mathematical-writing review](ENDPOINT_WRITING_REVIEW.md)
- [Current verification](ENDPOINT_VERIFICATION.md)

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
