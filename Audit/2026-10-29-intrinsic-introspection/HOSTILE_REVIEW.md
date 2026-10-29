# Hostile mathematical review

Date: 29 October 2026. Complete source reviewed by the drafting assistant
and a focused checker using HostileRefereeGPT — Cat/Rec instructions.

## (A) Kill-shots / hard blockers

No confirmed hard blocker remains. The main theorem locates its undecided
proposition in I, not in Glob(C), and uses no reflection or conservativity
assumption.

## (B) Major weaknesses

No major gap was established in the following checked interfaces:

- §1, equations (1)–(2): the internal hom is a correctly typed pullback;
  its points are precisely external arrows. The covariant functors H_C S_C
  and S_C H_C act on I and Glob(C), respectively.
- §1, comma construction: the left leg is arithmetic; the right leg need
  only be lex. Ramesh's left comma-stability therefore applies. Initiality
  supplies the unique N_C.
- Theorem 2.1: S_C preserves 0, so p_C=B_C0. Löb on the base rules out
  a refutation for every C. The global-hom identity makes noninhabitation
  exactly consistency of Glob(C), without a soundness premise.
- Corollary 2.2: Löb is applied separately in Glob(C). Its conclusion does
  not exclude a global point of Q_C0.
- Proposition 3.1: the internal-arrow formula for beta is composable;
  its naturality follows from the internal functor law and naturality of
  the arithmetic comparison. Uniqueness gives compatibility with N and
  coherence under composition.
- §3, initial models: restriction along i gives the target T-model;
  initiality supplies its model map, and the explicitly compatible AU
  interpretations give an internal arithmetic functor.
- §4: arithmeticity of global sections is used externally. Its internal
  failure at 0 is explicitly retained.

## (C) Minor issues

Finding: refutation wording. Anchor: §2, definition of undecided, original
phrase “The latter condition expresses refutation.” Failure mode:
`ambiguous`. Evidence: `derivation`; absence of p→0 is irrefutability,
whereas the arrow itself is a refutation. Severity: minor; no downstream
proof error. Resolved by “A morphism p→0 is a refutation; no pseudocomplement
object is required.”

The other checker requested explicit interpretation maps from the lex
theory of arithmetic universes and separate notation for the identity
functor and terminal object. Both clarifications were implemented.

## (D) Cross-section consistency failures

None remains in the checked source. The base I, global category L_C,
internal category C, and two modal functors remain distinct. The abstract
and main theorem locate undecidability in I. The final paragraph states
the unresolved essential-incompleteness claim in L_D accurately.

## (E) Acceptance conditions, non-negotiable

1. Retain the distinct source categories of B_C and Q_C. Met.
2. Retain arithmetic preservation of 0 in identifying p_C with B_C0. Met.
3. Retain the exact global-hom identity instead of assuming reflection. Met.
4. Retain the external/internal qualification on global sections. Met.
5. Do not claim first incompleteness of every Glob(D) from Corollary 2.2. Met.
6. Attribute the imported Löb, initiality, and internal-model theorems to
   Ramesh rather than claiming they are independently reconstructed. Met.

## (F) Not checked / uncertainty log

The displayed deductions and relevant primary-source statements were
checked. Ramesh's entire Löb proof and the Maietti/Vickers constructions
supporting the internal-model theorem were not independently reconstructed.
There was no exhaustive priority search or formal verification. The focused
checker did not inspect layout; the drafting assistant did so separately.

Strongest confirmed issue: corrected local refutation wording. No concrete
suspected mathematical blocker remains. The principal unreconstructed
inputs are the explicitly cited Löb and internal-model theorems, whose
statements were available. Final recommendation: **unknown**. The stated
deductions survived this author-side audit; external acceptance is not assessed.
