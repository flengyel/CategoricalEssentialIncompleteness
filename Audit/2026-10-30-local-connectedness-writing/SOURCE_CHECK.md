# Source check for the revised introduction

Baseline: commit `3f87a703c635c6c029f9c2bcb42aed5430ff8590`.
The revision concerns exposition, terminology, bibliography, and the name of
the manuscript. Existing model, lifting, and endpoint proofs retain their
earlier verification records. The checks below support the new literature
discussion; they do not assert priority for classical arithmetic incompleteness.

## LOCOct10f

The archived `manuscript/sources/LOCOct10f.tex` was read directly, including
its introduction, product-category conventions, local-connectedness argument,
range-functor lifting theorem, disjoint-arrow-join proposition, and the
counterexample when lifting is omitted. Its SHA256 is
`039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab`.
It is unchanged by this revision.

The revised introduction follows its historical progression from
Di Paola–Heller through Rosolini and Heller to the local-connectedness
method. Its first two sentences adapt the opening of that source.
The present paper includes the proofs it needs from the source, rather
than relying on an unpublished theorem without stating its hypotheses.
LOC Theorem 4.7, Proposition 4.8, and Section 4.5 distinguish the lifting
hypothesis, a sufficient disjoint-join condition, and the failure of the
other target hypotheses alone to imply lifting.

## Di Paola–Heller, Rosolini, Heller, and Bernardi

- Di Paola–Heller (1987), pp. 594–595: the publisher's opening extract
  states the generalized incompleteness program, including inseparability
  of theorem/refutation information. The manuscript attributes the program
  and does not claim to settle every formulation in that paper.
- Rosolini, *Representation theorems for P-categories* (1988), Theorem 1.2,
  pp. 307–308: the author's uploaded primary text realizes a P-category as
  a full P-subcategory of a category of partial maps with specified domain
  monomorphisms. The revision uses this representation context, not an
  unverified attribution of its own inseparability theorem to Rosolini.
  The 1986 thesis is identified as earlier background.
- Heller (1990), scan pp. 1264–1265, Sections 8–9: local connectedness
  enters the composition argument for Turing developments; Theorem 9.2
  supplies the generated recursion category under the stated data. No
  formula from the problematic printed p. 1262 is newly imported.
- Bernardi (1986), pp. 125–128: precomplete equivalence relations give
  inseparability results under his categorical hypotheses; the numerical
  examples include PA-provable program equality. The introduction states
  the numerical meaning of precompleteness, without applying Bernardi's
  dominical theorem to the nondominical category S_T or claiming a strict
  generalization of that theorem.
- Cockett–Lack (2002), *Restriction categories I*: the preliminary section
  states the four restriction axioms with a declared composition convention
  and explicit source/target conditions. The product pairing equations,
  restriction splitting, and domain order are typed in that convention.

## Lengyel 2004 together with its corrections

The original paper and the version-10 corrections were consulted together.
The corrections repository main was checked at
`5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b`. The cited source is
[`lengyel2004_repairs_v10.tex`](https://github.com/flengyel/errata/blob/5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b/lengyel2004/lengyel2004_repairs_v10.tex),
dated 20 October 2026.

The corrected existence argument uses a faithful **iteration functor**
preserving domains, coproducts, zero maps, and iteration, with a separated
target. Product preservation is not required. This is distinguished from
the range functor in the present inseparability theorem. Every substantive
mention of Lengyel2004 in the revised manuscript cites the corrections
alongside it. The historical citation is not used to discharge an additional
construction hypothesis in the present proof.

## The invalid pointwise quotients

The user requested
[Pointwise provable equality and the failure of composition](https://arxiv.org/abs/2609.25556).
The arXiv metadata and abstract were retrieved through search. Direct arXiv
opening was unavailable, so the statement and numbering were checked in
the author's full [version-37 source](https://github.com/flengyel/FailureOfComposition/blob/506d1f1494d6c05b0ba304edf5fe0bfa6c32864b/manuscript/failure_of_composition_2026-09-30_v37.tex).
The pointwise and uniform definitions and Corollary 2 were read directly.

Corollary 2 says that the proposed composition on S'_T is not well-defined
for any consistent c.e. extension T of PA, already for unary programs.
Montagna's S' is the case T = PA. This excludes these pointwise quotients
as categories under their proposed composition; it does not exclude the
uniform quotient S_T used in the manuscript.

The scan of Di Paola–Montagna (1991), printed p. 658, was inspected directly.
Corollary 4.4 is the non-local-connectedness statement for unprimed S_T.
Theorem 4.5 claims local connectedness of S'_T exactly under Sigma-1
soundness. Thus the new introduction identifies its arithmetic soundness
hypothesis rather than describing an unconditional local-connectedness
claim. The attribution is **Di Paola–Montagna**, not Di Paola–Heller.
The revised manuscript explains the two equivalence relations separately
and cites the composition obstruction precisely where it rejects the
primed construction.

## Limits of this check

These are source-grounded author-side checks. No new external peer review
or Lean formalization is claimed. The broader Di Paola–Heller program,
arbitrary recursion-category observations, and comparisons between changing
presentations remain outside the proved scope.
