# Mathematical Writing closure review of the numerical subsections

**PASS for the final version-26 candidate, §§7.4–7.5.** No necessary editorial, organizational, or explicit-type correction remains in the reviewed snapshot. The earlier reports record the source-grounded review and the concrete findings; this report verifies their closure on the resulting text.

The checked sources are frozen in `tmp/numerical26/round4/` and match the working manuscript files byte for byte:

| File | SHA-256 |
| --- | --- |
| `08c-numerical-realization.tex` | `28e6178cc451e2ff0de868c7c43872740d23d8dad74d337db3c96c7bb540378a` |
| `08d-numerical-incompleteness.tex` | `11d6c06139fa1b2b457d3c1a577026767afae0cd2121005eac5c3ef1ed9d98f8` |
| `08-essential-incompleteness-of-arithmetic.tex` | `a67c80632f8729caa0d0679e5b8bab260a5cdc4b20636ec9399ddb23ebdc247f` |

## Closure of the scalar-label issue

The final candidate now distinguishes three levels explicitly:

1. A numerical rule instance belongs to `|R_n^num|`; its stored label is a natural number in `widehat R_n^num` obtained using the tuple coding.
2. The corresponding interpreted syntactic rule instance belongs to `G_N R_n^syn`, through the typed bijection `rho_n` preserving the premise and conclusion maps.
3. A label stored in the syntactic derivation code belongs to the unary predicate carrier `C_n(N)⊆N`. The comparison `eta_n=G_N(u_n):C_n(N)≅G_N R_n^syn` is explicitly supplied by the chosen predicate presentation.

Consequently the forward stored-label transformation

`eta_n^(-1) rho_n kappa_mn^(-1)`

and its inverse

`kappa_mn rho_n^(-1) eta_n`

have the required numerical types. Both directions are computable on their declared carriers. The two rule comparison equations preserve child-premise matching and root conclusions, so the recursive tree transformations preserve validity and are inverse by induction on the finite tree. The conclusion equation for the resulting `rho_T` is typed between the distinct proof-code presentations. It is not an unsupported literal identification of the two proof carriers or an assumption that interpretation preserves an initial algebra.

The derivation-fold proof also now pairs child values with the **decoded rule instance** when forming a point in an inference-functor summand. This closes the accompanying local carrier distinction.

## Final exposition and type checks

The full reviewed argument retains the data needed by the author's explicit-type requirement:

- Objects of the total numerical category have dimensions and carriers; membership and computation statements use their carrier notation.
- The comparison functors `Q,F` have object and morphism actions. Their natural isomorphisms have typed components and naturality equations. The partial-map comparison is defined on spans, with the composition, restriction, fullness and faithfulness arguments stated.
- The arbitrary parameterized syntax algebra is declared in the correct product of slice categories. Its fold has typed components, projection equations and an algebra equation. The induction proves that the chosen partial recursive algebra programs halt on the relevant carrier inputs and proves uniqueness.
- The list fold uses its explicit canonical source isomorphism, empty-list value, nil/cons equations and uniqueness argument. The substitution algorithms refer to the fixed earlier codes and are identified with the categorical folds through their defining equations and uniqueness.
- The derivation carrier, constructor algebra, target algebra and evaluation fold are separately typed. Evaluation halts on valid derivation inputs because every intermediate result has the required conclusion and lies in the next algebra operation's source carrier.
- Sentence restriction is an explicit pullback. Appendix A supplies the image/least-theory argument; its general proof is not repeated.
- The incompleteness application has separately typed source idempotents, their images under the splitting inclusion, and the numerical sentence, substitution, negation and theorem-domain maps. The three comparison inequalities are located on their respective objects.

No new invented terminology, empty reassurance, editorial-process statement, or redundant defensive paragraph was found in these subsections. The details added to the proofs state mathematical constructions, types and equations. They should be retained rather than replaced by generic references to “the usual” evaluation or transport.

## Organization and rendering

Section7.4 has one purpose: establish the numerical realization and its logical-consequence objects. Section7.5 has one purpose: apply the numerical inseparable pair and domain-incompleteness corollary. Section7.6 then treats numeral instances and theory extension. The new files are input in that order, and the stable proposition label remains attached to Proposition7.7.

The final version-26 PDF has the realization on pages36–41 and numerical incompleteness on pages41–42. I rendered and visually inspected final pages39–42, covering the list and derivation folds, sentence pullback, rule/presentation comparisons, code transformations and the subsection transition. The displays, arrows, cross-references, page breaks and text are readable. Earlier layout inspection covered the leading categorical construction; the parent workflow performs the complete final build and page check. The current final LaTeX log contains no warnings or overfull/underfull boxes.

## Scope

This applies the actual KLR source and the author's typing and single-purpose requirements, with the source consultation and dependency checks recorded in `writing_r1.md`. It is a scoped review of these numerical subsections and the necessary imported definitions. It does not certify the whole manuscript, verify new literature claims, or establish a Lean elaboration. No Lean work or manuscript edit was performed by this reviewer.

**Unresolved necessary findings: none in the reviewed scope.**
