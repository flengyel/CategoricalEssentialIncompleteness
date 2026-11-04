# Author-side correspondence review — 4 November 2026

Scope: the new v46 Lean constructions, their dependencies and changed
correspondence rows. Separate agents performed source reviews; final
compilation, explicit statement checks and transitive axiom inspection
must be read from the accompanying verification record. This is an
author-side review, not a journal referee decision or an independent
kernel certification.

## (A) Kill-shots / hard blockers

No hard blocker was confirmed in the scoped completed constructions.
A claim that the entire v46 formalization is complete would fail: the
correspondence table explicitly retains unconstructed concrete syntax,
semantic and application obligations. Completed generic theorems do not
provide those missing instances.

## (B) Major weaknesses

1. **Exact syntactic presentation remains unproved.** Anchor: manuscript
   §5, Lemma 5.1, `05-syntactic-recursion-category.tex`, the exponential
   product pairing, even/odd coding and uniform trace formulas. The source
   specifies “Use the primitive-recursive pairing” before its displayed
   exponential formula, and Lemma 5.1 begins “For this computation coding”. Claim
   requiring a proof: identify the production category with that printed
   presentation. Failure mode: **unproved**, evidence: **structural_argument**.
   Production `CodedObjectMembership` uses square pairing and pair tags;
   `ConcreteEvaluator.eventualGraph` fixes a standard program index and
   quantifies an internal stage. The new source parity isomorphism and
   model graph equations recover the even/odd sum fragment. Exponential
   product and uniform trace comparisons are still missing. Downstream:
   whole-presentation claims and application identifications remain
   qualified. Severity: major for full completion; repairable by explicit
   PA-provable translations and comparisons. No counterexample to the
   mathematical lemma is claimed.

2. **Concrete first-order syntax, inference and soundness remain open.**
   Anchors: Propositions 5.5/5.7, Lemma 5.8, Theorems 5.9/6.6/7.3 and
   Proposition 9.3. Source anchors include `05a-internal-syntax.tex`,
   “Syntax initiality with parameters” and `lem:syntactic-derivation-initiality`,
   and `09-three-point-space.tex`, `prop:fork-proof-initial`: “The algebra
   $\delta$ is initial.” Failure mode: **unproved**, evidence:
   **absence_in_text** in the reported implementation, with explicit
   pending correspondence rows. The generic named syntax, substitution,
   inference and image theorems assume the initial algebras their printed
   definitions require. Actual standard validity/soundness and the
   Γ-provability instance are not constructed by the new generic partial
   lift or by ultrapower transport. Downstream: full categorical arithmetic
   and cosheaf H-presentation claims stay open. Severity: major for full
   completion; repairability requires the stated concrete constructions
   and proved named-variable/derivation comparisons.

## (C) Minor issues

1. **Resolved stale admissible-substitution status.** Anchor:
   `FORMALIZATION_STATUS_V46.md` at starting commit `ccd24e2073e6`,
   Definition A.1. It still listed generic admissible substitution as
   pending although the A.3 row and actual construction were proved.
   Failure mode: **inconsistent_use**; evidence: **derivation** from the
   two rows and `admissibility_complemented`. Severity: minor progress
   reporting defect. Repair: separate concrete initiality from the generic
   construction and identity laws.

2. **Resolved stale predicate-equivalence status.** Anchor: the same
   starting table, unnumbered §5 predicate-equivalence row. Its pending
   assertion contradicted the numbered 5.3 row. Failure mode:
   **inconsistent_use**; evidence: **derivation** from the actual
   `predicateEquivalence`, regular/extensive and mono-inverse declarations.
   Severity: minor. Repair: name the completed constructions and retain
   the distinct 5.1 presentation gap.

## (D) Cross-section consistency failures

The following boundaries were explicitly checked and preserved.

- The partial source lift is selected before the model and disjointness
  witness. Exact branch graphs use disjointness in the particular model;
  they do not require PA to prove it. The domain is their union and may be
  proper. The numerical parity comparison proves the actual even/odd
  source graph rather than identifying pair tags with parity by notation.
- The fixed syntactic comparison uses the actual typed Turing morphism,
  coproduct isomorphism and mapped diagonal bounds to apply Theorem 3.1.
  It does not assert the missing Γ syntax/soundness instance of 7.3.
- Deletion and substitution use internal truth fibers, arbitrary
  generalized parameters and actual parameter-slice initiality. Identity
  substitution returns the original quantified formula in the equal-name
  branch. The formula identity includes its actual admissibility lift. The
  quantified success subobject is proved at its actual pullback type; both
  monic coproduct summands have actual success lifts and result equations.
- Primitive-recursive reader graphs are total and coherent in every PA
  model, with a separate standard interpretation comparison. The selected
  defining program is not assumed PA-equivalent to every program equal
  to it only on standard inputs.
- List decoding starts with arbitrary actual slice algebras; no evaluator
  or initiality conclusion is supplied as a field. Set-valued model
  functors are used for finite geometry and faithfulness, without a claim
  of ordinary Set initiality for nonstandard internal lists.
- The numerical monic-span application uses the proved choice instance
  on the actual numerical-carrier category and its existing splitting
  equivalence. It does not insert an unproved global choice instance on
  `Split(Rec)`. Mono inverse equations and restriction-preservation
  comparisons are concrete obligations.
- Arbitrary c.e. propositional axiom closure is proved by a new explicit finite-record
  comparison. The old signed-atom proof semantics is unchanged. The
  individual endpoint extension conclusion has no compatible-family
  premise and does not by itself construct 9.3's initial H-algebra.
- Family coherence concerns all graph morphisms and the entire arithmetic
  model structure. Quotient and index-projection identities/compositions,
  pasted/direct squares and unitors are actual typed equalities.

No additional confirmed cross-section defect was found in these scoped
signatures. Unchecked application instances remain in section (B).

## (E) Acceptance conditions, non-negotiable

1. Every delivered module must compile warning-clean, with explicit
   statement checks at the reported object/morphism types and hypotheses.
2. The full verifier must retain imported-source/manuscript/dependency
   pins, the combined build, both v5/v46 statement audits, all strict
   v46 replays and complete transitive axiom coverage. The only permitted
   axioms are `propext`, `Quot.sound` and `Classical.choice`.
3. Every delivered production module must be reachable from the combined
   entry, and every statement check from the v46 audit. Incomplete drafts
   must remain outside production.
4. The tested input hashes must match the committed source bytes; the
   ordinary push and remote ref must be checked.
5. Reports and the table must retain all still-open concrete realizations.
   Dropping those qualifications would invalidate a full-v46 claim.
6. Report delivery must use the actual Windows Downloads directory and
   copies from committed bytes with verified hashes.

The full verification exited 0; all 404 tested input hashes
match proof commit `4b54dd15bd6b871d7211b749db259a16bae7055c`. The proof push
and remote ref check passed. Full command and axiom evidence is in
[the verification record](../V46_NEXT_PROOFS_VERIFICATION_2026-11-04.json).
The delivery receipt records the final report commit and copied hashes.

Failure of conditions 1–4 rejects the delivered proof batch. Failure of
condition 5 rejects a completion claim. A delivery failure must be reported
explicitly under condition 6.

## (F) Not checked / uncertainty log

This review does not prove novelty, certify the whole manuscript, perform
independent-kernel replay or registry verification, or revise/rebuild its
PDF. Existing unchanged mathematical proofs were not independently
reconstructed; the complete verifier rechecks their retained source and
axiom obligations. Source review and Lean verification are distinct.

The strongest confirmed blocker to full completion is the missing concrete
syntax/inference/soundness chain together with the exact 5.1 presentation
comparison. Strongest suspected unconfirmed blocker: none identified within the
scoped completed constructions. The most important unchecked work is
the remaining concrete realization and representation-independent Miller
application. The full-completion assessment depends on these unavailable
implementations. Final recommendation: **unknown** for the full v46
formalization; assess the delivered proof batch by the explicit conditions
and recorded checks above.
