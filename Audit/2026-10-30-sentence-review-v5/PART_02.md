# (A) Kill-shots / hard blockers

None confirmed in the assigned terminology, definition-order, typing, scope, and notation audit. This is an author-side audit of *Local connectedness, range functors, and essential incompleteness*, Version 5, 30 October 2026, against the immutable `build/sentence-review/baseline.tex`.

Every sentence, display, heading, proof, and source line in lines 296–518 was read. Lines 1–295 were read for prerequisites. The complete baseline was searched before evaluating potentially absent definitions. PDF pages 4–7 were checked through `baseline-pages.txt`; these are both the PDF and printed page numbers. There are no source comments in the assigned range.

The existing outline works:

| Section and source lines | Mathematical function and dependencies |
| --- | --- |
| Section 3, 296–381 | Defines formal numerical types, graph formulas, the quotient category, its restriction idempotents and ranges, and its Turing morphism. Uses the categorical definitions in Section 2. |
| Section 4, 383–431 | Defines interpretation in an arithmetic model and proves preservation of the categorical operations. Uses Section 3's uniform graph equality and graph identities. |
| Section 5, 433–517 | Defines the set of models and product category, proves faithfulness and the target properties, and defines the theory-extension comparison square. Uses Section 4 coordinatewise. |

No reorganization is recommended. The only confirmed finding is the local terminology inconsistency P02-01 below; it is not a mathematical blocker.

# (B) Major weaknesses

None confirmed within the assigned scope. No central term used in Sections 3–5 lacks a prior definition or an adequate local explanation. Standard vocabulary such as `Sigma_1`, primitive recursive, graph formula, countable model, faithful functor, and downward Löwenheim–Skolem is appropriate to the intended research audience and does not require a dictionary of definitions here.

# (C) Minor issues

**P02-01 — Retain the requested full term “restriction idempotents.”**

- **Anchor:** PDF p. 6, Theorem 5.1 proof, baseline lines 477–479; block B048.
- **Claim as written:** “These idempotents detect the definedness and value of every coordinate of a partial arrow.”
- **Failure mode:** `inconsistent_use`.
- **Why it fails as written:** The referent is mathematically unambiguous, because the preceding sentence explicitly says “restriction idempotent.” Nevertheless, the shortening conflicts with the user's express requirement to use “restriction idempotents.” This is a terminology requirement, not evidence of an erroneous proof or a missing mathematical distinction.
- **Evidence:** `structural_argument`: the constructed arrows are coordinatewise partial identities, and hence are precisely restriction idempotents; comparison with the immediately preceding sentence exhibits the shortening.
- **Counterexample or missing hypothesis:** None; no mathematical hypothesis is missing.
- **Downstream impact:** None for the mathematics. The correction keeps the terminology consistent with Section 2 and the requested vocabulary.
- **Severity:** Minor.
- **Repairability:** Direct local replacement.
- **Exact repair:** Replace the quoted sentence by:

  ```latex
  These restriction idempotents detect the definedness and value of every
  coordinate of a partial arrow.
  ```

The explicit user preference supplies the rationale for this edit. Knuth–Larrabee–Roberts, Section 1, points 11 and 14, support introducing variables and maintaining consistent notation; those points do not themselves prohibit this otherwise harmless anaphoric abbreviation.

# (D) Cross-section consistency failures

None confirmed beyond P02-01. The following checks record adequate introductions and prevent the audit from manufacturing missing-definition findings.

| Term, notation, or construction | Introduction and uses checked | Status |
| --- | --- | --- |
| Composition order | Line 159 specifies `gf=g\circ f`; the graph-composition identity at 323–332 and later functor laws use that order. | Consistent. |
| Restriction idempotents, their order, and complements | Lines 171–188 precede `[C]_T`, its order, and joins at 345–355. | Adequately defined before use. |
| Restriction, range, and agreement | Lines 190–203 define the operations and agreement law; lines 355–368 instantiate them with existential graph formulas. | Types and roles agree. |
| Products, coproducts, and Turing morphism | Lines 219–241 and 285–294 precede the constructions at 370–381. The parameter arrow has the required totality and type `X\to\omega`. | No new, unexplained universal property is introduced. |
| `T`, `\N`, `\omega`, formal numerical types | Lines 298–303 introduce their meanings and coding assumptions before the quotient category. `T` need not be c.e. here; c.e. is explicitly added for the cited non-local-connectedness assertion at 489. | No silent strengthening of the standing hypothesis. |
| Typed program index versus category morphism | Lines 304–308 define graph formulas for typed indices; lines 310–319 then introduce equivalence classes `[e]_T`. | The annotation `e:X\rightharpoonup Y` is explicitly attached to a **typed program index**, so it is not an undeclared identification of an index with its quotient class. |
| Uniform versus pointwise equality | Equation (1), lines 312–318, gives a single quantified theorem; lines 334–343 explicitly distinguish the primed relation. | Distinction is expressed before either is used to justify composition. The factual external claim was not reverified in this focused audit. |
| `[C]_T` versus `[e]_T` | Line 346 expressly introduces `[C]_T` as the restriction idempotent of the witness-search program. | Declared, readable shorthand; not unexplained overloading. `D` in equation (3) is the second formula of the same kind. |
| `R_e` | Introduced by `R_e(y):=\exists x\,G_e(x,y)` at 359; used at 364 and 424. | Definition precedes use. |
| `\Pfn` | Defined already at 261–262 and restated constructively at 385–388. | No missing or late definition. |
| `X_M`, model codings, and standard numerals | Recursive object interpretation at 390–398 precedes the morphism interpretation. The text distinguishes a standard index's numeral from arbitrary model elements and later distinguishes a numeral's value from its carrier label at 437–438. | No numeral/carrier or standard/nonstandard drift. |
| `F_M:S_T\to\Pfn` | Object and morphism actions are given at 399–403; source, target, and covariance are stated in Proposition 4.1 at 407–411. The proof verifies representatives, identities, and composition at 414–419. | Adequately explicit functor data. The variable types follow from the typed program and recursive interpretation; no missing-definition finding. |
| `\mathcal M_T` and `\mathcal D_T` | The index **set** is defined at 435–441. The product category, object families, morphism families, and coordinatewise operations are specified at 443–449. | Explicit indexing. This is a product indexed by a set; there are no omitted nonidentity indexing morphisms or naturality conditions between distinct models. |
| `F_T:S_T\to\mathcal D_T` | Both object and morphism actions appear at 452–453. | Covariance and functor laws follow coordinatewise from the already specified `F_M`. |
| Connectedness, splitting, partial monomorphism, section, weak choice | Definitions at 205–215 and 264–276 precede the assertions and proofs at 460–486. | No late definition. The proof uses connected partial identities, subsets as splitting objects, and inverses of coordinatewise injections. |
| “Singleton objects supported at one coordinate” | Line 482, after the product category is explicitly defined and singleton-supported partial identities have been described at 475–477. | Standard finite-support shorthand for the family with one singleton coordinate and empty coordinates elsewhere. No new paper-specific object class is being invoked. |
| `Q_{T,T'}` | Lines 495–502 specify source, target, object action, morphism action, variance, and well-definedness. | Typed covariant functor; quotient-class action is explicit. |
| `\pi_{T,T'}` | Lines 503–505 define restriction of both object and morphism families from `\mathcal M_T` to its subset `\mathcal M_{T'}`. | Explicit indexing operation and source/target; no unspecified “transition map.” |
| Commuting comparison square | Lines 505–517 fix interpretations once and show that both paths produce the same `T'`-model family. | Strict equality is justified by the stated fixed choices, rather than inferred from mere isomorphism. |

The functor checks made in this scope are the following. Uniform equivalence is respected because each model satisfies the universal graph-equality sentence. Composition under `F_M` is the same existential composition of partial-function graphs, with identities interpreted as identities. `F_T` inherits these laws in every model coordinate. `Q_{T,T'}` respects equality because a proof in `T` is also a proof in `T'`. Restricting a family twice has the same object and morphism values as restricting it directly, which gives the laws for `\pi`; the square's two routes retain exactly the same representatives and coordinates. These checks confirm the displayed types and variance; they are not a certification of the paper's full mathematics.

No occurrence of “transition map” or “structure map” occurs in the assigned range. “Arrow,” “morphism,” and “partial function” are used in their appropriate categorical or set-theoretic roles. The description of a theory-indexed family does not claim an unnamed additional functor from a theory category in this range, so no such definition is missing.

# (E) Acceptance conditions, non-negotiable

1. For compliance with the user's explicit terminology instruction, replace “These idempotents” at line 478 by “These restriction idempotents.” The deliverable is the one-sentence repair in Theorem 5.1's proof; the endpoint is a direct source check of that sentence. Failure would leave a minor editorial noncompliance, **not** grounds for rejecting a mathematical theorem. No mathematical claim needs to be dropped.

No major reconstruction or additional hypothesis is required by the findings of this focused audit. No main-source edits were made.

# (F) Not checked / uncertainty log

- **Coverage:** Every assigned block B032–B051 was read in full, including displays and proofs. The companion JSON records exactly the blocks whose first line lies in 296–518. Surrounding definitions were read at lines 1–295, and the entire baseline was searched for relevant vocabulary and definitions. A complete-source mathematical review was not performed.
- **Source consultation:** The HostileReferee instructions, the mathematical-writing skill and its two supporting references were read. The supplied `loc_knuth_section1_excerpt.txt` was consulted, including Section 1, points 5 and 10–17. The report uses verified guidance on self-contained statements, variable introduction, reading order, and notation. It does not attribute its A–F audit format or the user's terminology rule to that source.
- **External results:** The cited Montagna/Di Paola–Montagna assertions, the primed-composition paper, and the PA formalization assumptions were not reverified against their primary sources in this focused terminology pass. No new claim about their truth, novelty, or adequacy is made here.
- **Render check:** PDF-extracted page text for pages 4–7 was inspected to locate the audited material. No new compilation, graphical PDF inspection, or layout certification was performed.
- **Possible optional clarifications, not findings:** One could repeat `x\in X_M`, `y\in Y_M` beside (4), or replace “singleton objects supported at one coordinate” by “families with a singleton at one coordinate and the empty set elsewhere.” Existing definitions already determine these meanings, so neither addition is demanded as a missing-definition repair. The typed-index notation at 304 is expressly declared and should not be condemned merely for resembling arrow notation.

**Final self-audit:** Strongest confirmed blocker: none; the strongest confirmed issue is minor P02-01. Strongest suspected but unconfirmed blocker: none identified in the assigned terminology/typing scope. Most important thing not checked: independent verification of the programming formalization and cited external mathematical results. The local terminology finding does not depend on unavailable material. Final recommendation: **unknown** for journal acceptance because this was a restricted terminology and definition-order audit, not a full correctness or novelty review.
