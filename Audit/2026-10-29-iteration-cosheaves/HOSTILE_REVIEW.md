# Hostile mathematical review

Date: 29 October 2026.
Target: manuscript/iteration_domains_and_cosheaves.tex, §§1–7.
Method: author-side audit using the HostileRefereeGPT — Cat/Rec instructions.
The same assistant drafted the note and conducted this audit. Subsequent
focused checks by two other agents are recorded in FOCUSED_CHECKS.md.
No human referee or formal proof checker was invoked.

## (A) Kill-shots / hard blockers

No unresolved hard blocker was established for the stated bounded-arity
results after the corrections below. This is not a certification.

The following stronger readings must be rejected:

- **Arbitrary fixed points give least finite syntax.** Theorem 4.1 does not
  use this inference. It constructs termination domains r_m and proves
  e_n ≤ r_(B_n) and r_m ≤ e_m, preserving agreement as well as order.
- **Heller's generated recursion category inherits every ambient range.**
  This is false in the cited simplicial example. §1 expressly separates
  the ambient existence theorem from range closure. §6 proves its own
  computational range closure.
- **Cosheaf products are pointwise on every space.** §7 supplies the
  discrete two-point counterexample. §6 restricts the componentwise
  calculation to Sierpiński cosheaves, where the arrow-category equivalence
  is proved.

## (B) Major weaknesses

1. **Termination without selected support.** Checked Theorem 3.1:
   the finite trace object is an equalizer inside the nonempty-word object
   of the split domain, not an assumed external coproduct of all traces.
   Its length pieces identify with dom(εf^n). Range of the start map
   supplies the union; endpoint descent uses a covered kernel pair.
   No arbitrary countable union is assumed.
2. **Order suprema substituted for agreement unions.** Checked Lemma 2.3
   and Theorem 4.1. The graph argument explicitly transports agreement.
   The cofinal inequalities transfer the agreement condition. Finite joins
   and composition of covers were made explicit during review.
3. **An epic range factor called regular without descent.** Checked
   Theorem 2.2: the range of (q,h) projects monically to the image of q;
   pulling its full-range cover back twice proves that monicity.
   Weak choice makes the projection an isomorphism. This supplies the
   kernel-pair coequalizer, followed by its pullback stability.
4. **Decidable equality reintroduced in the consistency proof.** Checked
   Lemmas 5.1–5.2 and Theorem 5.3. The equivalence relation is an external,
   finite relation on positions in a fixed formula shape. It is generated
   by required equalities, not computed by deciding arbitrary labels.
   A Boolean valuation is used only in this finite propositional argument.
   The resulting equality chain is then a categorical equality on the
   branch object. Additional actual equalities do not invalidate it.
5. **Unbounded shape of logical axiom parameters.** Lemma 5.1 refines
   each fixed proof shape by the syntax covers of all its finitely many
   formula parameters. It does not impose a global shape bound on a
   recursive family of formulas.
6. **Nonnumerical example merely a disguised numerical category.**
   Proposition 6.3 distinguishes the total categories by three versus
   two terminal subobjects. The universal object's transition is
   noninjective and its equality cannot be decided naturally.
   This differs from the two-phase example in the cited errata.
7. **Universal evaluator fails naturality or changes the represented
   domain.** Proposition 6.2 filters the component-0 computation by the
   component-1 result. Naturality of the represented partial square proves
   that this extra test succeeds exactly wherever its component-0 program
   halts. The compiler square is total and commutes.

## (C) Minor issues

Confirmed and corrected:

- The initial abstract omitted the finite-limit, extensive, product-range,
  and stable-length qualifications. It now states them.
- A reference to the errata's corrected union calculus was §10.2;
  the source places it at §11.2.
- The splitting equivalence in §6 initially had an ambiguous antecedent
  (“its splitting”). It now names the splitting of R_→.
- Finite joins and composition of shape covers were previously implicit.
  Their universal-agreement proofs are now written before use.
- The new trace theorem is explicitly identified as a reconstruction of
  Heller's Lemma 7.1.
- The fixed finite arity bound is defined in §4; no theorem about an
  unbounded-arity polynomial is asserted.
- The subsequent consistency check requested an explicit finite refinement
  of nullary leaf labels by their signed-axiom/logical-scheme tags.
  Lemma 5.1 now includes that extensivity argument.

## (D) Cross-section consistency failures

Checked the following interfaces; no remaining failure was established:

- Theorem 4.1 discharges both unions used by the existing initiality theorem,
  not the Turing-fold theorem itself.
- The cited Turing fold remains filtered by the type-equality range, with
  strength restricted to total program parameters.
- Logical negation is the constructor ν; ν* is monotone inverse image
  on domains, not domain complementation.
- Theorem 5.3 requires the constructed finite-stage proof algebra. It does
  not assert soundness or consistency for arbitrary extensions.
- §6 verifies all hypotheses in the restriction splitting. Its isotypical
  full subcategory is the recursion category; the two are distinguished.
- The 23-page note, the 13-page supplement, and the Lean development
  retain their earlier statements and verification status.

## (E) Acceptance conditions, non-negotiable

For the scoped paper claims:

- Retain finite limits, extensivity, universal product-compatible ranges,
  weak choice (or the separately stated factoriality alternative), and
  stable finite-length coverage. Do not weaken them silently.
- Retain bounded finite arity and the explicit size/height comparison.
- Retain the finite-shape refinement in the equality-free consistency proof.
- Retain the evaluator's compatibility filter and exact-domain argument.
- Attribute Heller's iteration lemma and range failure, and the corrected
  Lengyel graph/range calculations. Do not claim a priority result without
  a separate literature investigation.

For a broader claim covering general generated recursion categories or
nontrivial cosheaf covers, a new proof of computational closure is required.
That claim is not accepted by the present argument.

## (F) Not checked / uncertainty log

The entire new source was read; the principal proofs were reconstructed
as described above. All final pages were rendered and inspected separately
for layout. The prior supplement was consulted at its committed version.
Targeted source scans were checked as recorded in SOURCE_CHECK.md.

Not checked: all of Heller's existence proof, all errata claims, Rosolini's
original representation proof, general coalgebra generated-subcategory
closure, a nontrivial-cover cosheaf evaluator, arithmetic interpretation,
or novelty against all literature. None is used as an unproved premise
for the explicit Sierpiński construction. No Lean formalization exists.

Strongest confirmed defect was the initial abstract's understated hypotheses;
it is corrected. The most important remaining unchecked direction is
closure of general generated recursion categories under the constructions.
The cited materials used were available, but no independent referee report
or machine-checked proof was available.

**Publication recommendation: unknown.** The scoped proofs survived this
author-side audit; publication acceptance requires independent mathematical
assessment. A claim to have completed the general Di Paola–Heller program
would require major reconstruction.
