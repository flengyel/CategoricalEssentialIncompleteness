# Mathematical writing review

The manuscript has a coherent dependency order: domains and ranges, stable unions, deductive closure, representation and inseparability, and arithmetic realization. The local typing and notation findings from the initial review have been resolved and checked in a complete rereading of the final source. No substantive editorial finding remains open, and no change of outline is recommended. The source contains no editorial-process, correction, or LLM-facing remarks.

## Source and scope

- Manuscript: *Deduction and essential incompleteness in recursion categories*, dated 29 October 2026, `manuscript/deduction_and_essential_incompleteness.tex`.
- Read in full, including the abstract, diagram, proofs, and bibliography, and then reread completely after the authoring agent implemented the findings. Final reviewed source SHA-256: `8b5a92b888bd08bb627e5280442c6fb45dc5172726905b618fe58f72f6ce07c0`.
- Governing source consulted: Knuth, Larrabee, and Roberts, *Mathematical Writing*, supplied local text, Section 1 (printed pp. 1–6) and Sections 4–5 (printed pp. 9–13).
- Verified source advice used here: Section 1, point 5, on self-contained theorem statements; points 10–13, on connected explanation, introducing variables, motivation, and prose that survives skimming formulas; point 14, on consistent notation; point 17, on unambiguous reading. Sections 4–5 explicitly allow contextual flexibility in definition placement, while requiring definitions near use.
- The user's requirement to declare functors before their assignments, and the requirement for fully typed categorical data, are applied as project requirements rather than attributed to Knuth.

## Current outline

| Section | Function and dependencies |
| --- | --- |
| 1. Domains and ranges | Establishes partiality, domain order, range universal property, direct image, inverse image, and the partial-map form of the adjunction. |
| 2. Stable unions and inverse image | Defines Heller's stable unions; proves meet, image, and inverse-image laws; obtains the bounded distributive lattice-valued domain functor and finite-power continuity. |
| 3. Deductive closure and theories | Defines parameterized rules and finite stages; proves least rule-closed extension from stable chain unions; restricts conclusions to a selected domain; defines theories and the reflector. |
| 3.1. Morphisms of presentations | Defines continuity, the category `Cons`, the contravariant theory functor, and the natural inclusions of closed domains. |
| 4. Representation and essential incompleteness | Defines the negative domain, consistency, completeness, relative separators, and representation; proves inseparability and essential incompleteness; proves inheritance of representation. |
| 5. The arithmetic realization | Defines the partial-recursive model, domains and ranges; verifies stable unions of uniformly c.e. families; exhibits the obstruction to arbitrary countable unions. |
| 5.1. Effective deduction | Realizes the abstract rules by modus ponens and parameterized generalization; proves uniformity of stages and identifies the selected closure with arithmetic theoremhood. |
| 5.2. Representation and arbitrary base theories | Supplies syntactic negation, joint numeral substitution, and strong numeralwise representation; proves the arithmetic corollary for possibly non-c.e. bases by transfer to a consistent c.e. extension. |

The main result is the essential incompleteness theorem for the fixed points of the constructed closure. The closure theorem depends on ranges and stable unions of the generated chains. The inseparability theorem depends on the representation equations and inverse-image preservation of finite joins. The arithmetic corollary uses both results and the transfer of numeralwise definability under extension.

## Comparison with the governing source

| Manuscript anchor | Initial finding | Principle or rationale | Verified resolution |
| --- | --- | --- | --- |
| Section 1, preliminary domain-poset notation | The initial source used `E(X)` before declaring the functors. The user expressly requested functor-first presentation. | Project typing convention; Section 1, point 14 supports distinguishing roles of notation. | The preliminary poset is now `Dom(X)`. Both `E_!` and `E` are declared with source and target before their object and morphism assignments. |
| Proposition `prop:effective-union` | The common ambient power of the natural numbers was omitted from the statement. | Section 1, points 5 and 11; explicit typing requirement. | The statement now fixes `r≥1` and `A_k⊆N^r`. Its proof types `δ:N^{r+1}⇀N^{r+1}` and `π_2:N^{r+1}→N^r`. |
| Theorem `thm:inseparability` | The phrase “the conditions above” left the substitution assumptions as a diffuse backward reference. | Section 1, point 5. | The theorem now states both morphism types, the two support equations, and the restriction equations expressing totality on the appropriate domains. |
| Section 5.1, rule names | The generalization rule and a later representative both used `g`. | Section 1, point 14. | The numerical rules are now consistently named `mp` and `gen`, while `g` denotes a representative. |
| Paragraph proving inheritance of representation | The zero subscript was malformed. | Typographical correctness. | The source now has `0_{U\boxtimes U}`. |
| Final proof of `cor:arithmetic` | “Both kinds of proving instances” was unidiomatic. | Section 1, point 17; Sections 4–5 on precision of wording. | The text now says that the positive and negative instances remain provable under extension. |
| Bibliography entry `RestrictionI` | The entry was uncited. | The writing skill's literature-purpose requirement. | It is now cited at the introduction of the restriction notation. |

## Definition order and notation audit

- Composition is fixed before use, and the restriction equations state their typing conventions.
- Domains, the domain order, ranges, and stable unions are defined before the corresponding lemmas.
- Stable unions are attributed to Heller (1990). The definition includes both the parallel-arrow universal property and product stability.
- The preliminary domain-poset notation is `Dom(X)`. The two domain functors have explicit variance and are declared before their object/morphism assignments, satisfying the user's stricter presentation order.
- The rule morphisms have explicit arities, parameter objects, and support equations. Nullary rules are assigned to the fixed axiom domain.
- The selected domain `s` is a restriction idempotent. The abstract construction does not assert a categorical object of sentences or introduce an abstract notion of an open formula.
- Closure, theories, extension, the reflector, continuity, and the contravariant theory functor are introduced in their dependency order. The direction `b≤t` is correctly stated to mean that `t` extends `b`.
- The negative operation is typed before the negative domains. No syntactic double-negation identity is imposed.
- Consistency, completeness, relative complement, separation, and representation are defined before the main theorem.
- Arithmetic formula and sentence codes occur only in the numerical realization. The distinction between these domains serves the generalization rule and selected conclusions.
- Uniform c.e.-ness is defined in the union proposition and justified for the deduction stages. The nonuniform counterexample contributes a necessary distinction and should be retained.
- The final arithmetic statement explicitly permits a non-c.e. base. Its proof transfers the representation premise to the c.e. extension, whose theorem domain is represented categorically.

## Final-source checks

The final source contains the typed replacements recorded in the table. The inverse-image lemma now explains that its output union is stable, after establishing the union property. The nonuniform-family paragraph states the exact conclusion that arbitrary increasing countable families need not have unions; it does not claim that uniformity is necessary for every individual existing union. The substitution paragraph describes the terminating algorithm jointly in the formula index and numeral input, including the absence of variable capture for a closed replacement term. These additions state mathematical dependencies directly and introduce no editorial commentary.

## Scope and verification limits

This is a complete-source editorial review, not a certification of the mathematical results or originality. The parent review handles the independent mathematical audit, compilation, rendered-page inspection, and source verification of the mathematical citations. This report does not claim those checks. No Lean source or proof replay was examined. The final-source rereading and the recorded resolutions apply to the source hash above.
