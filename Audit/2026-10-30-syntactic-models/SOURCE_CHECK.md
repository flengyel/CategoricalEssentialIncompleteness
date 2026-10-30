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
