# (A) Kill-shots / hard blockers

No fatal or major mathematical blocker was found in the final source of *Deduction and essential incompleteness in recursion categories*, dated 29 October 2026.

The complete source was examined in the independent mathematical and arithmetic reviews. The final reviewed source SHA-256 is `8b5a92b888bd08bb627e5280442c6fb45dc5172726905b618fe58f72f6ce07c0`. This is an author-side source-level audit, not a journal decision or a proof-assistant verification.

# (B) Major weaknesses

None confirmed. The central proof dependencies were checked as follows.

| Anchor | Typed construction and law checked | Evidence and result |
| --- | --- | --- |
| Section 1, Definition 1.1 and Lemma 1.2 | A range of f:X→Y is a restriction idempotent on Y with the receiving and parallel-arrow agreement properties. | Derivation: uniqueness, least receiving domain, range of a domain, composition, and multiplication by a codomain restriction follow from the stated universal property. |
| Section 1, direct image and equation (5) | E_!:R→Pos sends f to e↦ran(fe). The inverse-image map is d↦bar(df). | Derivation: monotonicity and functor laws follow from range identities. The partial-map adjunction retains e bar(f); an unqualified adjunction is asserted only for total f. |
| Section 2, Definition 2.1 | Heller unions include agreement of arbitrary parallel arrows; stability is under 1_W⊠−. | Structural argument: the exact universal definition is retained, rather than only the order-theoretic supremum property. |
| Section 2, Lemma 2.2 | Multiplication by a fixed domain and direct image preserve unions; total inverse image preserves stable unions. | Derivation: the graph range R=ran⟨1,h⟩ and direct image along π₁ give h*d. The final product-factor argument proves stability of the output union. |
| Section 2, Lemma 2.3 | Finite powers, with an optional fixed parameter factor, preserve the union of an increasing stable chain. | Derivation: a mixed finite tuple of indices is bounded by its maximum; coordinatewise stability then gives the universal union property. |
| Section 3, Theorem 3.1 | Positive finite-arity partial rules act on domains by ranges; fixed axioms account for nullary rules. | Derivation: the union lemmas establish rule closure of the stage union; induction gives leastness; monotonicity, extensivity, and idempotence follow. Only the specified stage chains require countable stable unions. |
| Section 3, selected closure and reflection | c_s(a)=s c_q(a) for a≤s; L:E_s→Th_c is left adjoint to inclusion. | Derivation: c_s(a)≤c_q(a) proves idempotence with monotonicity and extensivity. The adjunction is exactly c_s(a)≤t iff a≤t for closed t. |
| Section 3.1 | Cons has arrows total on the selected source domain and satisfying the continuity inequality; Th:Cons^op→Pos restricts inverse image. | Derivation: support conditions and continuity compose; inverse image preserves closed domains. Inclusion naturality is equality of the same restricted maps. Closure is not claimed automatically natural. |
| Section 4, Theorem 4.2 | The representation equations refer to b and bar(bν). Separators are complementary relative to s. | Derivation: δ=σΔ is total with δ*s=1. The representation square produces equal complementary pullbacks, contradicting 0_U≠1_U. |
| Section 4, Theorem 4.3 | An extension has b≤t, hence b⁻≤t⁻. | Derivation: consistency and completeness would make (t,t⁻) a separator. No involution equation or closure-preservation condition for ν is used. |
| Section 5, Proposition 5.1 | Uniformly c.e. A_k⊆N^r give a c.e. tagged domain whose projected range is their union. | Derivation: partial-function agreement, including definedness, proves Heller's universal property; products give stability. |
| Sections 5.1–5.2 | Parameterized generalization, uniform stage indices, finite proof trees, and joint numeral substitution realize the categorical data. | Derivation: sentence selection gives actual theorem domains. Strong numeralwise definability gives the exact two representation equations. |
| Corollary 5.2 | A possibly non-c.e. base transfers strong definitions to each consistent c.e. extension T. | Derivation: apply the categorical theorem to the domain representing T itself. No computational domain for the original base is assumed. |

# (C) Minor issues

No findings remain outstanding.

Two mathematical exposition findings were resolved in the final source:

1. **Lemma 2.2(3), page 3:** the initial graph calculation established the union property without explicitly verifying its stability. The final proof applies the argument to 1_W⊠h and uses associativity and the restriction-product identity to verify the missing clause. Evidence: derivation. Initial severity: minor; resolved without additional assumptions.
2. **After Proposition 5.1, page 7:** the initial wording could be read as making uniformity necessary for every individual existing union. The final text states precisely that arbitrary increasing countable families need not have unions and supplies the finite approximations to a non-c.e. set. Evidence: counterexample. Initial severity: minor; resolved.

The separate writing review verifies the common ambient numerical power, functor-first presentation, explicit substitution types, rule names, and local notation.

# (D) Cross-section consistency failures

None confirmed. The audit checked the following distinctions throughout:

- Computational domains versus arbitrary predicates; theories are closure-fixed restriction domains.
- Partial morphisms versus total maps used for preservation of top and complementary pairs.
- Complements relative to s versus complements with top 1_U.
- Existential representatives versus a computable procedure choosing indices.
- Uniformly generated deduction chains versus arbitrary countable families.
- Arithmetic open intermediate formulas versus the abstract selected-domain construction.
- A possibly non-c.e. base versus its c.e. extension, which is the domain to which the categorical theorem is applied.

No monoidal enrichment or completion is claimed. Turing universality identifies the numerical computational setting; it is not used to infer the independent representation hypothesis.

# (E) Acceptance conditions, non-negotiable

All source-level endpoints identified by this audit are met: the output-stability argument is present, the uniformity statement has its exact scope, and the representation and nontriviality hypotheses remain explicit.

Retain the explicit representation premise in Theorems 4.2–4.3. Any stronger assertion that arbitrary recursion categories or arbitrary consistent theories are essentially incomplete would require a separate proof.

Machine verification of this note may be claimed only after its exact new constructions are implemented and checked in Lean. That endpoint is not part of the present manuscript delivery.

# (F) Not checked / uncertainty log

The review is source-level mathematics. No Lean file was changed, built, or axiom-audited as part of this review. The parent separately compiled the final source and visually inspected all nine pages.

The range and stable-union definitions were compared with the cited PCats sources. The complete original Heller and Di Paola–Heller papers were not independently reread by this reviewer. No novelty or exhaustive historical-program claim is certified.

The arithmetic algorithms were checked mathematically, not by an executable encoding test. The note realizes the Q and PA theorem domains but does not itself prove the separate strong numeralwise representability theorem for those theories; Corollary 5.2 explicitly assumes the needed property.

Final self-audit: strongest confirmed blocker—none; strongest suspected unconfirmed blocker—none identified; most important unchecked item—the implementation of the new construction in Lean and the separate representability specialization to Q or PA. The source-level conclusion does not depend on unavailable material. Final recommendation: **unknown** as to publication acceptance or complete formal verification; no rejection-level mathematical defect was found in the stated conditional results.
