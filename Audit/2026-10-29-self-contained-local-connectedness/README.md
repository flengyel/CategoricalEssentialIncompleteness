# Self-contained local-connectedness paper

The paper is
[Local connectedness, range functors, and essential incompleteness](../../manuscript/local_connectedness_and_essential_incompleteness.pdf)
([source](../../manuscript/local_connectedness_and_essential_incompleteness.tex)).
This revision replaces the private-note citations by the arguments needed
in the paper, including the claims made in its introduction.

The local-connectedness and range-functor theorem retains its lifting
hypothesis. Section 6 also states and proves the sufficient criterion
using joins of arrows with disjoint domains. That criterion was already
proved in Proposition 4.8 of the author's private local-connectedness note;
the deficiency was its omission from the preceding version of this paper.
Appendix C concerns precisely the statement obtained by dropping the
lifting hypothesis, not the theorem with that hypothesis retained.

Appendix A constructs the computational fork category, its ranges and
other structural operations, explicit frames, Turing morphism, and the
restriction-splitting equivalence. Appendix B constructs finite syntax
and proof objects, their conclusion range, and the consistency argument.
The paper uses no free range completion. The restriction splittings it
does use are defined and their comparisons are proved explicitly.

The sentence citing Lengyel2004 and its corrections now says directly
that preservation of the near product is not required. This was already
true in the original paper, as its printed page 27 expressly states.

- [Outline and dependency inventory](OUTLINE.md)
- [Source checks and internal proof locations](SOURCE_CHECK.md)
- [Mathematical-writing review](WRITING_REVIEW.md)
- [Hostile mathematical review](HOSTILE_REVIEW.md)
- [Build and delivery verification](VERIFICATION.md)

The reviews are author-side checks. The current revision supplies the
arguments behind earlier private-source references; it does not claim
new priority for those arguments or formal verification in Lean.
The [preceding writing record](../2026-10-30-local-connectedness-writing/README.md)
and [model and endpoint records](../2026-10-30-syntactic-models/README.md)
remain historical records of their reviewed versions.
