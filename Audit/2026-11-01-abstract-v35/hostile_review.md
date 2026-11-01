# Abstract: mathematical and typing check for version 35

Scope: revised descriptions of the three logical realizations, their categorical setting, the Di Paola–Heller motivation, and the comparison and extension mechanisms. Unchanged application claims were not re-audited. This supersedes the earlier opening-only check at the same path.

## (A) Kill-shots / hard blockers

None found.

## (B) Major weaknesses

None found.

## (C) Minor issues

**Anchor:** abstract, comparison paragraph, “Soundness makes these interpretations disjoint.”

**Claim as written:** soundness entails disjoint interpreted theorem and refutation domains.

**Failure mode:** ambiguous.

**Difficulty:** Proposition 4.1 uses two premises: a soundness factorization through a validity subobject and disjointness of that subobject from its inverse image under syntactic negation. A factorization alone does not give disjointness. The required disjointness is proved for the arithmetic interpretation in Proposition 6.6 and transported in Theorem 6.9, so the constructed applications are supported. The abstract's generic sentence suppresses this distinction.

**Evidence:** structural argument and manuscript statement. For the bare factorization condition, take a two-element sentence object S in Set, let negation interchange its elements, and let both the designated validity subobject and theorem subobject be all of S. The conclusion morphism 1_S factors through the designated validity subobject, but the theorem subobject meets its negated inverse image in all of S. Thus factorization alone is insufficient.

**Repair:** “A soundness factorization through a validity subobject disjoint from its negated inverse image makes these interpretations disjoint;” followed by the existing total-reduction and partial-conditional-lift clause. A shorter statement restricted to the established instances is: “For the sound interpretations constructed here, the theorem and refutation domains are disjoint;”.

**Downstream impact:** qualification of the abstract's comparison mechanism only. The body already states and verifies the condition. Severity: minor. Repairability: direct local replacement.

## (D) Cross-section consistency failures

No additional failure found.

- First-order logic **with equality** is realized in the total restriction splittings of the syntactic recursion categories (Theorem 5.9) and Miller's recursion category (Proposition 8.5), using Appendix A's first-order calculus and equality axioms.
- Propositional logic is realized in the three-point cosheaf completion (§9.3 and Appendix A.6).
- Each categorical realization takes place in a regular category of total morphisms of a restriction splitting, as explicitly typed in §4.1 by \(\mathscr S=\operatorname{Split}(\mathscr R)\) and \(\mathcal D=\operatorname{Tot}(\mathscr S)\).
- Initial algebras describe syntax and finite derivations; Theorem A.5 identifies the regular image of the initial derivation algebra's conclusion morphism with the least rule-closed subobject. Theorem A.6 supplies the first-order specialization.
- The comparison sentence retains both the total reduction and the lift of a partial conditional, matching Theorem 4.2. The separate consistent-extension sentence matches Corollary 4.3.
- The Di Paola–Heller clause states that the results address their program; it makes no universal priority or complete-realization claim. The program is explicit in Di Paola–Heller, §1, pp. 594–595: the categorical/algebraic development is intended to formulate generalized incompleteness, and the listed consequences include incompleteness of every consistent r.e. extension.

## (E) Acceptance conditions, non-negotiable

Qualify the soundness-disjointness sentence as above. No further round is needed if the exact categorical qualification is inserted or the assertion is restricted to the established sound interpretations.

## (F) Not checked / uncertainty log

No fresh audit of the body proofs or unchanged application claims was undertaken. The Di Paola–Heller motivation was checked against the cached primary text, §1, pp. 594–595. Strongest confirmed blocker: none; the one local ambiguity is recorded above. Strongest suspected blocker: none within the checked scope. Most important unchecked matter: a complete fresh body-proof audit, outside scope. No unavailable source affects this comparison. Final recommendation on the whole manuscript: **unknown**; after the local qualification, no concrete mathematical or typing objection remains to the revised passages.
