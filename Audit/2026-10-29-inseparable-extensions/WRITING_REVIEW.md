# Mathematical-writing review

Date: 29 October 2026. Manuscript: *Inseparable domains and computational
extensions*, final source and five-page PDF dated 29 October 2026.

This is a complete-source, author-side editorial review. The organization
fits the mathematical dependencies: domain reductions precede the free
signed construction, its exact extension classification, the application
to existing classical theories, and the distinction between functorial
reflection and preservation. No reorganization is needed. The principal
repairs concern typed notation and precise reference locations.

**Provisional source status.** The mathematical-writing plugin requires
Knuth, Larrabee, and Roberts, *Mathematical Writing*, as its governing
source. A fresh request for the official Stanford report
`https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf` timed out;
the parent author's requests for that report and its bibliographic page
also timed out. Earlier project records report consultation of a supplied
copy, but that copy was not available for this review. The findings below
therefore use explicit editorial reasoning and the plugin's independent
typing and economy conventions. They are not claimed as freshly verified
applications of numbered rules or quotations from the book.

## Actual outline and mathematical functions

| Part | Function and dependency |
| --- | --- |
| Abstract | States the signed construction, exact equivalence, classical extension application, and failure of unrestricted forward preservation. |
| §1, Domains, separators, and reductions | Defines restriction domains, total inverse image, separation, and the category of ordered disjoint pairs; proves transport by a total reduction. |
| §2, The free involutive presentation | Proves coproduct decomposition of domains; defines involutive presentations and their morphisms; constructs the adjunction; classifies consistent and complete extensions. The final paragraph states the substantive boundary with the classical calculus. |
| §3, The fixed interpretation for classical extensions | Constructs the extension-poset functor and the fixed natural family of atom maps; identifies its data in the existing one-node proof diagrams; treats unsplit assertion domains and the previously established construction hypotheses. |
| §4, Functors between computational categories | Proves reflection under domain-preserving functors and preservation under bijection on endomorphisms; gives the diagonal-product projection counterexample and distinguishes Heller's prodominical definition from the dominical subclass. |
| References | Identifies the earlier construction manuscripts and Heller's definition used for the counterexample. |

Every prose paragraph has one of the functions in this table: definition,
proof, construction, application, comparison, or mathematical limitation.
The source contains no reviewer instructions or drafting narrative.
The signed/classical distinction is a substantive limitation and must
remain. The statement about the stronger inseparability conclusion is a
comparison with a specific earlier theorem, not a claim of originality.

## Findings and repairs

| Anchor | Difficulty | Editorial rationale | Recommended repair |
| --- | --- | --- | --- |
| §1, “contravariant functor on `Tot(R)`” | The target category is omitted although both actions are supplied. | A claimed functor should have an explicit source and target. | State `Tot(R)^op -> Pos`, defining `Pos` as posets and monotone maps. |
| §2, first paragraph and Theorem 2.2 | The initial notation defines `a+b` only for endomorphisms, but the construction uses `f+f` for an arbitrary total map. | Define notation at its full type before the later use. | Define `f+g=[i'_0 f,i'_1 g]:X+Y -> X'+Y'` for `f:X->X'` and `g:Y->Y'`; specialize to domains afterward. |
| §2, definition of an involutive presentation | “Its elements are understood as assertions” suggests a set-based interpretation not provided for an arbitrary restriction category. | Describe the categorical role without introducing undeclared underlying elements. | “Regard `S` as the object of assertions; `nu` forms their negations, and `t` selects the theorems.” |
| §3, first cited one-node proof paragraph | “Corollary 7.3” is the wrong number in the current general supplement. | Readers must be able to locate the precise prior construction. | Cite Corollary 6.3, label `gen:essential`. |
| §3, unsplit-domain paragraph | The earlier declaration gives `nu:S->S`, while this paragraph applies it to domains on `V`. | A change of ambient object requires an explicit declaration and restriction support. | Add `nu:V->V`, `bar(nu)=s`, and `s nu=nu` before writing `nu* t`. |
| §3, relative-transfer citation | “Theorem 7.1” is the wrong number in the original note. | Same reference-location requirement. | Cite Theorem 6.1, label `ct:certificate-transfer`. |
| §3, final paragraph | “verified nonnumerical instance” can read as verification-process commentary. | State the mathematical applicability directly. | “is a nonnumerical instance satisfying these hypotheses.” |
| §4, opening paragraph | “has the other direction” is imprecise because total inverse image and the domain action of a functor have different categorical types. | Name the variance directly. | “its induced map on domains is covariant.” |

The two reference numbers were checked against the current source
section counters and the shared theorem counters. Unchanged manuscripts
were not rebuilt for this purpose. All eight recommendations were
implemented by the parent and checked in the final source. The unsplit
paragraph also explicitly defines `nu* t=bar(t nu)` for its partial
negation constructor. No unresolved editorial correction remains from
the table.

## Definition order and notation audit

- Composition, restriction, totality, domain order, meets, bounds, and
  inverse image precede the separation definition.
- `Pair(R)` has explicitly given objects, total morphisms, inequalities,
  identities, and composition. The reduction direction is consistent
  with the inverse-image direction in its proof.
- Restriction coproducts and their injections precede domain
  decomposition. The revised general arrow-sum declaration supplies the
  type needed by `Sigma(f)=f+f`.
- `Inv(R)` specifies the involution, consistency equation, equivariant
  total arrows, and theorem-domain containment before `J` and `Sigma`
  are introduced. The hom-set bijection, unit, and counit are typed.
- The signed-extension definition precedes its equivalence theorem.
  The theorem assumes exactly the domain joins needed there; its proof
  uses the coproduct order isomorphism rather than asserting general
  inverse-image preservation.
- The classical section introduces `theta`, `nu`, `t_0`, the two base
  inequalities, and the extension poset before the functor and natural
  transformation. It distinguishes monotone inverse image under the
  negation constructor from logical complementation.
- The one-node proof diagram names each arrow with its source and target.
  The subsequent range argument uses the existing split-domain objects;
  the paper does not enlarge the selected domain class.
- The functor-between-categories section introduces `F`, its direction,
  and its action on domain idempotents before stating reflection.
  The revised counterexample names the source category, arrow equality,
  structural actions, evaluator, projection, and nonzero image pair.

## Priorities and retained exposition

The ambient type of the unsplit negation constructor and the two
reference numbers are necessary corrections. The coproduct-arrow
notation and target of the domain functor complete the explicit typing
requested for this project. The element wording and variance sentence
are local improvements, not claims that the associated proofs are false.

Retain the order-isomorphism proof, the explicit extension-poset
classification, the hom-set bijection for the adjunction, and the single
atom-map interpretation for all extensions. They each establish a
distinct mathematical claim. Retain the boundary between signed literals
and a classical Hilbert presentation: removing it would change the scope
of the result. Retain the prodominical/dominical distinction in the
counterexample because it determines the category class to which the
negative result applies.

## Rendering and review scope

All five pages of the initial compiled PDF and all five pages of the
final PDF were visually inspected. Text, mathematical displays, the
one-node proof diagram, references, and page margins were legible; no
clipped or overlapping content was observed. The final log had no LaTeX
warnings or overfull/underfull box messages. The final inspected files
have SHA-256 hashes:

- Source: `56f1c3fb3f24ca0c0fea2e47820e13c5237352fa83c92eea9b9052d79820d431`.
- PDF: `bccb0087214ebdd65640dcfb79fcf8162288602d5a14cd844321be9433b3d684`.

This review does not certify the proofs, establish novelty, or replace
the mathematical audit. It does not independently recheck the earlier
classical construction manuscripts or Heller's scanned definition; those
source and mathematical checks belong to the accompanying focused
reviews. The entire final manuscript source was reread continuously
after the repairs, including the final range and iteration explanation
in the projection counterexample.
