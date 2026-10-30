# Version 5: introduction, framework, and attribution

30 October 2026.

The abstract states the contribution directly, without suggesting that a
“local-connectedness method” is an established method in the literature.
It names the syntactic recursion categories of Di Paola and Montagna,
uses “a section-lifting condition,” and introduces the arithmetic
consequence with “It follows that.”

The introduction was checked against the supplied *Locally connected
recursion categories*, LOC18Jul06.tex. It restores the motivation through
Heller's local connectedness hypothesis, the Di Paola–Montagna examples,
and the range-functor approach to non-locally connected source categories.
The earlier manuscript supplies the expository model; the present theorem
retains its section-lifting hypothesis.

The introduction now names Montagna's S and S', and Di Paola–Montagna's
S_T and S'_T. It identifies S with S_PA, retains the uniform quotients,
and explicitly excludes the primed systems because their proposed
composition fails to descend to equivalence classes. Section 3 gives
that reason directly, without an unused soundness qualification.

Related work is a separate subsection, distinct from the statement of
this paper's Theorem 6.3. It records the progression from Di Paola–Heller's
dominical categories to Rosolini's P-categories, Heller's prodominical
categories, Cockett–Lack's restriction categories, and Cockett–Hofstra's
Turing categories. The framework used here is restriction categories,
with binary restriction products in the source recursion categories.
Cockett–Lack III, Proposition 4.5, supplies the exact comparison with
P-categories. Both that paper and Cockett–Hofstra (2008) are now cited.

The earlier inseparability results of Di Paola–Heller and Bernardi remain
credited. Montagna's Remark 3.1, printed p.114, also gives effectively
inseparable pairs in the unprimed S; this is now acknowledged explicitly.
No first-existence claim is made for S.

## Source checks and verification

- The supplied LOC18Jul06.tex introduction was read directly.
- Heller (1990), Section 5, printed pp.1260–1261, explicitly adopts
  Rosolini's P-categories and defines “prodominical.”
- Di Paola–Montagna, p.644, motivates the extension of Heller's theorem;
  p.646 distinguishes the two syntactic equalities, and Corollary 4.4
  supplies the failure of local connectedness for the stated S_T.
- Montagna (1989), p.114, Remark 3.1, was checked against the scan.
- Cockett–Lack III, Proposition 4.5, was checked in the primary preprint;
  the publisher records confirm both new bibliographic entries.
- The prose review used Knuth–Larrabee–Roberts, *Mathematical Writing*,
  Section 1, particularly motivation, definition order, and attribution.

This revision changes introductory prose, two explanatory passages in
Section 2, the primed-system discussion in Section 3, and the bibliography.
The theorem, proposition, lemma, corollary, and proof environments,
displayed mathematics, and labels are unchanged from Version 4.
The focused checks do not constitute a new audit of all proofs.

The exact delivered source was compiled with latexmk. The 28-page PDF
has no compilation warnings or overfull/underfull boxes. The affected
opening pages and bibliography were inspected. Source and PDF hashes
are recorded in [DELIVERY_V5.json](DELIVERY_V5.json).
