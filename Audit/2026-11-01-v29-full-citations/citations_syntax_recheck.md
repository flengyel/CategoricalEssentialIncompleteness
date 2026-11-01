# Scoped recheck of syntax citation corrections

Scope: only the three HP/HH changes in `tmp/audit_v29/corrections.diff`, plus fullwriter C1 concerning Appendix A lines 169–175. This is not a new audit. Existing cached primary texts and the original citation-audit evidence were reused. No manuscript files were edited.

## Corrected HP and HH passages

| Passage | Result | Primary-source comparison |
|---|---|---|
| HP bibliography: “2017 reissue of the Springer text, originally published in 1993” | Pass | CUP catalog dates print publication to 2 March 2017 and online publication to 24 March 2017. The CUP frontmatter is ©2016; the Springer original is ©1993, with a later 1998 softcover. The revision resolves the prior copyright/publication-year ambiguity. |
| HP pinpoint: `\cite[0.10, p.~7]{HP}` | Pass | The three propositional axiom schemata are in numbered paragraph 0.10 on printed p.7. The revised locator is exact. |
| HH attribution: “their reflexivity and substitutivity principles with terms as parameters” | Pass | HH §3.1 pp.64–65 gives variable reflexivity and variable substitutivity in formulas, subject to the free-for restrictions. The new wording accurately identifies the principles and makes v29’s term-parametrized presentation an adaptation rather than a verbatim transcription of the source axioms. |

The three changes resolve all qualifications attached to these passages in `citations_syntax.md`. No further correction is required for them.

Evidence:

- HP publisher excerpt, 0.10 p.7: <https://assets.cambridge.org/97811071/68411/excerpt/9781107168411_excerpt.pdf>.
- HP CUP catalog: <https://www.cambridge.org/core/books/metamathematics-of-firstorder-arithmetic/E72D370D90F316D86CB9D0927377A1A3>.
- HP CUP frontmatter: <https://assets.cambridge.org/97811071/68411/frontmatter/9781107168411_frontmatter.pdf>.
- HP Springer record: <https://link.springer.com/book/9783540636489>.
- HH full author text: <https://appstate.edu/~hirstjl/primer/hirst.pdf>, §3.1 pp.64–65.

## Fullwriter C1: scope of the alpha-equivalence statement

**Confirmed for all three cited treatments.** The statement that these treatments identify expressions up to renaming of bound variables is true in context. No narrowing is required to correct a false attribution.

| Source | Actual primary-text support | Exact scope |
|---|---|---|
| Fiore–Plotkin–Turi | §2, author PDF p.5, defines the presheaf `TVα(n)` using alpha-equivalence classes, immediately before Theorem 2.1. | This is stated for general binding signatures, not just the lambda-calculus example. Its nameless implementations represent the same classes. |
| Gabbay–Pitts | §6, Theorem 6.2, author PDF p.15, identifies the inductively defined FM-set `Λα` with lambda terms modulo alpha-conversion. The concluding §6 discussion, author PDF p.20, extends the construction to binding signatures. | The source also introduces raw terms as an intermediate object. Its binding-syntax object used for the initial-algebra treatment represents alpha classes. Having raw terms in the development does not contradict the manuscript’s contextual summary. |
| Katsumata | §2, author PDF p.4, explicitly identifies alpha-equivalent terms in the definition of the typed formal system, immediately before Example 1. | The convention governs all the examples, including Example 1(3), the first-order logic signature with an existential quantifier. |

Primary texts:

- FPT: <https://www.dcs.ed.ac.uk/home/dt/FiorePlotkinTuri.pdf>.
- Gabbay–Pitts: <https://www.gabbay.org.uk/papers/newaas-jv.pdf>.
- Katsumata: <https://www.kurims.kyoto-u.ac.jp/~sinya/paper/generalpre.pdf>.

This confirmation concerns their binding-syntax objects. It does not assert that these sources construct v29’s raw named-variable syntax in an arbitrary category or prove its parameter-stability assumption. V29’s following sentence expressly distinguishes its named syntax and admissibility subobject, so the comparison remains accurate.

Cached evidence remains in `tmp/audit_v29/evidence/syntax/`, including full PDFs, extracted text, Gabbay–Pitts page images/OCR, and download provenance.
