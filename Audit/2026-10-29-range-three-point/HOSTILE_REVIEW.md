# Hostile mathematical review

Date: 29 October 2026. Scope: the complete companion note.

This author-side review applies the HostileRefereeGPT — Cat/Rec plugin
instructions. A focused proof checker reconstructed §§2–6 and the internal
obstruction argument; a separate checker examined the range-completion
sources. Their scope and remaining uncertainty are recorded below.

## (A) Kill-shots / hard blockers

No confirmed hard blocker remains in the reviewed claims.

The most delicate external dependency was the discrete completion's span
normal form. Construction 3.21, Lemma 3.22, and the extension formula in
Theorem 3.27 were checked against the CGH primary text. The identity-extension
justification was then added explicitly. The independent three-point
construction does not depend on a general completion theorem.

## (B) Major weaknesses

No major internal gap was established. The following interfaces were tested:

- Proposition 2.1: every basic-open cover contains that open; the unique
  additional cover condition is the global pushout. Span maps extend uniquely.
- Proposition 2.2: representable finite probes detect component injections.
  Image descent is natural by cancellation of componentwise epimorphisms.
  Universal agreement reflects both partial domains and values through
  the surjective maps onto the component images.
- Lemma 4.2: the word frame retains the entire sequence of component indices,
  including words whose letters belong to different components. Its coordinate
  coding is invertible and commutes with both transitions.
- Theorem 5.1: the central filter makes arbitrary programs into a partial
  diagram. For a compiled diagram F, its own domain inclusions and naturality
  guarantee both checks, so the filter removes no point of F's domain.
- Lemma 6.2: complementary subdiagrams partition every basic component.
  Complete bipartite incidence forces an entire k-block into one part.
  A fixed endpoint representative decides the resulting index partition.
- Theorem 6.3: the constructed category supplies every structural hypothesis
  used from the preceding iteration and consistency note. The typed filter
  and total-parameter strength restriction are explicitly retained.

## (C) Minor issues

### Finding 1: uniqueness only up to isomorphism

- Anchor: Lemma 1.1, use of the extension formula for η.
- Failure mode: `missing_justification`.
- Evidence: `source_check`; CGH's theorem states uniqueness up to isomorphism.
- Impact: the displayed normal-form equality needed an explicit bridge
  from universal uniqueness to equality of the two extension functors.
- Severity: minor, repairable.
- Resolution: lift the identity transformation on η; because η is identity
  on objects, the isomorphism has identity components and the functors agree.

### Finding 2: unused hypothesis

- Anchor: Proposition 1.2, original universality of τ in the source category.
- Failure mode: `unused_hypothesis`.
- Evidence: `derivation`; the proof only uses that τ is an arrow, universality
  of Jτ, and lifting of total program maps.
- Impact: no invalid conclusion; the stated assumption was unnecessarily strong.
- Severity: minor, repairable.
- Resolution: remove the unused source-universality hypothesis.

The product comparisons in Proposition 1.2 and four notation/definition
clarifications identified by the writing review were also made explicit.

## (D) Cross-section consistency failures

No remaining failure was found in the checked interfaces.

Global quotient equality is not assumed decidable. A categorical mono may
be noninjective at the whole space, and §3 gives the explicit 2→1 example.
Products, words, and syntax are internal basic-diagram constructions followed
by pushout. The component index is retained in all three frames. Failure
of decidable equality is compatible with binary case distinction because
complementary domains consist of whole incidence blocks. Theories remain
computational domains, with selected categorical theorem ranges.

## (E) Acceptance conditions, non-negotiable

1. Verify the exact external completion hypotheses and normal form. Met
   by the separate primary-source check; no regularization claim is used.
2. Retain the distinction between categorical domains and pointwise global
   subsets. Met by §3 and the explicit mono counterexample.
3. Retain the component index and full component-word coding. Met by Lemma 4.2.
4. Retain both endpoint tests and the exact-domain proof. Met by Theorem 5.1.
5. Retain stable length coverage, the typed fold, and total-parameter strength.
   Met by Proposition 2.2 and the stated application in Theorem 6.3.
6. Do not conclude a general recursion-preserving completion theorem. The
   final paragraph states this limitation and the next construction question.

## (F) Not checked / uncertainty log

The focused proof checker did not independently verify the CGH citations
and therefore returned **unknown** for the complete note, while finding no
internal blocker in the three-point construction. The separate completion
checker and drafting assistant checked those sources and repaired the
identity-extension step. This division of work is not human refereeing.

The preceding finite-stage, equality-constraint, and Turing-fold proofs were
not re-proved in this review; their existing verification and conditional
statements were reused. No exhaustive novelty search, formalization, or
general recursion-preserving completion proof was performed.

Author-side disposition: the requested corrections are resolved and the
note is suitable for committing within its stated scope. External acceptance
remains **unknown**. Neither these reviews nor PDF compilation is a
machine-checked proof of the mathematics.
