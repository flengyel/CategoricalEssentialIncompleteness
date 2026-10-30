# Source check

Repository baseline: 3be65406b0bb6d3109a41fd3f517ca62fcc5ed8f.

## LOCOct10f

Florian Lengyel, *Locally connected recursion categories*, revised
10 October 2026. The entire supplied LaTeX source was retrieved; the
mathematical comparison concerns §§3.1 and 4.1–4.5. Its SHA-256 is
039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab.
The source is preserved without changes at
[manuscript/sources/LOCOct10f.tex](../../manuscript/sources/LOCOct10f.tex).
It is not relabelled as a new contribution.

- Connected domains and local connectedness: §4.1.
- Sections and weak choice, partial monicity, and total switching: §4.3,
  labels PropPartialMono, PropCopOut and PropDichotomy.
- Range-functor inseparability theorem: Theorem 4.7, label ThmRecIns.
- Sufficient lift by disjoint-arrow joins and failure of lifting:
  §§4.4–4.5.

The new note reconstructs the connected-domain alternative using inverse
images of the summand domains. Its lifting proof takes inverse images in
the target directly, retaining the source's theorem hypotheses. Product
preservation by the functor is not used. A lift need not be total in the
general theorem; the model application supplies a total lift explicitly.

## Syntactic categories

The earlier source and graph calculations in
[SYNTACTIC_SOURCE_CHECK.md](../2026-10-29-separator-transfer/SYNTACTIC_SOURCE_CHECK.md)
were reused. Their primary sources are Montagna (1989), pp.105,108,111–114,
and Di Paola–Montagna (1991), pp.646–647.

The DPM §4 text was reread. The scan of printed p.657 was inspected,
confirming Theorem 4.3 and Corollary 4.4: no S_T in its stated consistent
c.e. class is locally connected. This assertion is made about S_T, not
about the product target. The invalid primed systems are not used.

No soundness hypothesis is introduced. Every graph, trace, intermediate
value, and image witness is interpreted in the whole model. The carrier
N of a model is not assumed to have standard arithmetic operations.

## Other inputs and scope

- First-order completeness and countable downward Löwenheim–Skolem supply
  models on carrier N and distinguish unproved uniform equality sentences.
  Their metatheoretic use is explicit.
- The three-point category's existing structural verification is reused
  from the unchanged source at the repository baseline. Its local
  connectedness is proved here by finite generated subdiagrams; fullness
  gives the lift.
- Bernardi's PA program-equivalence example and precomplete-equivalence
  theorem remain credited to the 1986 paper, pp.125–128. No new
  precompleteness claim is made.
- The writing review consulted the supplied Knuth–Larrabee–Roberts
  *Mathematical Writing*, §1, printed pp.1–3 (PDF pp.3–5).

This is a focused source comparison and proof audit, not an exhaustive
novelty search or a new formalization of the underlying machine semantics.

## Introduction and endpoint continuation

Baseline: faf3d070c94681748b6cb99d22243173bd665644.

The Introduction of the preserved LOCOct10f source was reread. Its order
of motivation is retained: Di Paola–Heller's program, the role of ranges
and local connectedness, the precise lifting requirement, and the
syntactic categories that are not locally connected. The new paper then
states the additional effective argument giving essential incompleteness.

The publisher's primary-source extract of Di Paola–Heller (1987) was
consulted at
https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/dominical-categories-recursion-theory-without-elements1-2/2E11506A81794B06EF34603881D79394 .
It explicitly states the algebraization objective and includes recursive
inseparability of theorem/refutation sets among the generalized
incompleteness statements. The date used is the September 1987 print
publication, not the publisher's later online-hosting date.

The unchanged three-point source and its PDF were checked at:

- Proposition 2.1: cosheaves are covariant fork diagrams, with a pushout
  at the whole space.
- Proposition 2.2: finite limits, componentwise monomorphisms and images,
  regularity, weak choice, and the split partial-map structure.
- Sections 4–5: the universal fork V, frames, and the explicit Turing
  morphism. Its endpoint formulas are used verbatim as mathematical
  data, and their classical parameter universality is proved separately.
- Proposition 6.1: five terminal subobjects and failure of decidable
  equality on V.
- Theorem 6.3: the consistent finite-proof presentation.

The three Hilbert schemes were checked against the displayed schemes
in iteration_domains_and_cosheaves.tex, Section 5, including the
orientation of the classical contraposition scheme.

The new component-evaluation, probe, separator, and extension arguments
are proved directly. They invoke no new Heller equation, no range
completion theorem, and no preservation of the proof polynomial by an
observation functor. Earlier source verification is reused for the
unchanged finite-proof construction.
