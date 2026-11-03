# Inseparable domains and computational extensions

Date: 29 October 2026. Base: `main` at
`b20c3d89757a692314413e7d83fcf4511a4f3b22`.

The five-page [note](../../manuscript/archive/inseparable_domains_and_extensions.pdf)
([source](../../manuscript/archive/inseparable_domains_and_extensions.tex)) develops
the requested two functor directions and constructs a minimal presentation
inside the given restriction category.

The principal concrete result is the free involutive presentation
`Σ(U,a,b)=(U+U,swap,a+b)` and its adjunction to the positive/negative-pair
functor. With binary domain joins, the signed presentation is essentially
incomplete among selected domain extensions if and only if `(a,b)` is
inseparable. Its base consistency follows directly from `ab=0`; this part
does not have an unproved nonvacuity premise.

The classical application reuses the actual atom and one-node proof maps
in the committed sources. It strengthens their conclusion to inseparability
of every consistent extension's theorem/refutation pair. It does not derive
the classical proof algebra or its consistency from the minimal signed
construction. Classical deductive closure over the signed presentation
remains a candidate to test against the primary target recorded below.

The reflection result assumes preservation of restrictions, zero, and
binary domain joins. The preservation counterexample is the second
projection from a diagonal-object subcategory of the product of two
numerical recursion categories. It preserves the chosen evaluator, ranges,
and iteration. Its source satisfies Heller's 1990 prodominical definition
and is not dominical. The target still has other inseparable pairs.

Records:

- [Outline and dependencies](OUTLINE.md)
- [Hostile author-side audit](HOSTILE_REVIEW.md)
- [Provisional mathematical-writing review](WRITING_REVIEW.md)
- [Source checks and prior work](SOURCE_CHECK.md)
- [Build and verification](VERIFICATION.md)

These are author-side reviews, not independent human referee reports.
No new theorem is Lean-formalized. Earlier mathematical sources and PDFs
are unchanged.

## Subsequent research direction

The user has selected separator transport from an extension-associated
category D_T back to the starting recursion category C as the primary
construction target. The [continuation document](../../CONTINUATION_GENERAL_RECURSION_CATEGORIES.md)
now states the direct functor direction G_T:D_T→C, the required
theorem/refutation-domain inequalities, and the consistency/completeness
connection. The source-grounded program assessment is in
[PROGRAM_SOURCES.md](../2026-10-29-program/PROGRAM_SOURCES.md).
The signed construction remains a proved preliminary result; it is not
a replacement for this intrinsic connection to formal systems.
