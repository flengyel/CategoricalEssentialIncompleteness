# Evidence-bound audit of the Google review

Scope: the four concrete objections to manuscript v58, compared with the
identified source/PDF and current Lean statements. The original report and
hashes are preserved in the accompanying assessment.

(A) Kill-shots / hard blockers

No mathematical blocker is established by the supplied objections.

The alleged malformed partial-monomorphism condition, anchored by the report
at Section 2.2, p.5, is not the condition in the source or rendered page.
The existing condition is `pu=pv` implies `bar(p)u=bar(p)v`, with
p:X to Y and u,v:W to X. Both consequent morphisms have type W to X.
Evidence: `derivation` by this type calculation; `citation` to Cockett–Lack I,
Section 2.3.1, p.238; direct source/PDF comparison. Disposition: answered by
the existing text. No mathematical repair is warranted. The two Lean
definitions quantify over every W and agree definitionally by the existing
compatibility theorem.

(B) Major weaknesses

No major defect is established. The global-section suggestion concerns the
exposition of an explicit hypothesis, not its absence.

Anchor: Section 5.3, pp.16–17, construction of E_U and Theorem 5.3.
The fixed point `lambda_U:1 to U` gives E_U B_U naturally isomorphic to the
identity and allows every rule's premises to be evaluated in one fiber.
A sentence-dependent map k:S to U would instead give, after base change
and forgetting, E_k(B_U X) isomorphic to S times X. This does not supply the
retraction used in the theorem. Evidence: `derivation` from the two pullbacks.
The existing arbitrary-slice Lean checks use the fixed point and impose no
constancy condition on the extension. Disposition: answered by the existing
construction; no extra article remark is necessary.

The suggested abstract version of Theorem 8.6 would require an additional
statement specifying its indexed axioms, uniform conditional lift, reduction
and consistency interpretation. The printed theorem explicitly fixes the
arithmetic realization and constructs those data. Evidence: the statement
and displayed parameterization in Section 8.3. Disposition: a possible
further generalization, not a defect in the stated result. No stronger
theorem or extra hypothesis is inserted.

(C) Minor issues

Anchor: bibliography [18], p.86. Claim: University breaks after its first
letter. Failure mode: `ambiguous` typography, severity minor, repairability
local. Evidence: `toy_test` by rendering the exact v58 PDF page; the source
spelling and bibliographic data are correct. Downstream impact: layout only.
Version 59 keeps University unbroken. The rebuilt page has been inspected.

(D) Cross-section consistency failures

The report's transcription of the partial-monomorphism formula differs from
both the source and PDF. No corresponding inconsistency exists between the
definition and the downstream partial-monic arguments or Lean definitions.

The phrase “without local connectedness” is in the report, not the manuscript.
The introduction retains one substantive comparison with Heller. No
defensive sentence is added elsewhere.

The report's blanket mathematical approvals do not complete the seven open
Lean rows. Theorem 5.3 stays complete; Lemma 8.9 stays open until its actual
signed-theory consistency and essential-incompleteness clauses are proved.

(E) Acceptance conditions, non-negotiable

1. Preserve the correctly typed partial-monomorphism condition and the
   universal test-object quantifier. Failure would require rejecting the
   affected mathematical statements as written.
2. Preserve the fixed-point hypothesis and arbitrary closed slice-extension
   quantifiers of Theorem 5.3. Failure would invalidate a claimed match to
   its existing proof and formalization.
3. Verify the publisher repair on the rebuilt PDF and synchronize the
   manifest/archive. Failure leaves the minor typesetting defect open.
4. Mark Lemma 8.9 proved only after every printed clause has an actual Lean
   counterpart and the permitted-axiom checks pass. Failure rejects a
   completion claim; it does not refute the manuscript's mathematical proof.

(F) Not checked / uncertainty log

This audit adjudicates the report's four concrete items and the wording
question. It does not reconstruct all 77 proofs or repeat the 32-entry
primary-source audit. The report's summary of 23 verified papers and nine
non-paper entries supplies no new per-reference evidence. No novelty or
priority conclusion is adopted from its strengths section.

Strongest confirmed blocker to a claim of full Lean formalization: the
seven rows already recorded as open. Strongest suspected unconfirmed
mathematical blocker: none identified in the reviewed objections. Most
important unchecked matter for Lemma 8.9: the concrete positive-support
assignment and valuation comparison proving internal consistency. The four
dispositions do not depend on missing mathematical text; exact identity of
the external upload is known only through the reported version and matching
pagination, not an upload hash. Final recommendation for the whole paper:
unknown. The concrete review items require only the recorded typesetting repair.
