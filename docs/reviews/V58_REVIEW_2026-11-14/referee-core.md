# Repeat core referee review — v58

Reviewed files: `revision-v58/manuscript/latex/`, compared with the pinned v57 source `dfe6d3b9b948875d9d268ef8bbd332d65c6b53e5`. Scope: §§2–5 and Appendix A, together with the changed decidable-equality convention and its proof in Appendix B. No manuscript files were edited by this reviewer.

## Functional outline and comparison with the text

1. §2 defines the partial-map setting, ranges, products/coproducts, completion and Turing structures. It is unchanged.
2. §3 proves the computational comparison and complementary-conditional inseparability criteria. It is unchanged.
3. §4 represents generated internal theories, applies the comparison criterion, then constructs generation/Galois/free-theory adjunctions. Its only change specifies the Boolean quantifier operation in Corollary 4.8.
4. §5 constructs Turing partial slices, theory-extension functors and their adjunctions, and the constant-family incompleteness comparison. Its only change removes two repeated summaries following Theorem 5.3.
5. Appendix A supplies syntax, lists, substitution, finite-rule algebras, regular-image generation and their specializations. It is unchanged.
6. Appendix B’s final convention now takes the true fiber of the equality decider, matching Appendix A; its following proof uses that same summand.

The text follows this dependency order: Appendix A → §4 generation; §2 → §3 comparison; §4 and §5 categorical hypotheses → associated incompleteness. The amendments do not alter it.

(A) Kill-shots / hard blockers

No confirmed hard blocker was found. A literal comparison verified that all 22 numbered statements and definitions in the core scope, and all ten numbered statements in Appendix B, are unchanged. The previous 19-proof reconstruction was checked against those unchanged source bytes, not assumed merely from a version label.

(B) Major weaknesses

No confirmed major mathematical defect was found. The current corrections add no hypotheses, weaken no conclusions, and change no quantifier.

(C) Minor issues

The prior minor omission in Corollary 4.8 is resolved. At `sections/03b-internal-adjunctions.tex:350–353`, universal quantification is now explicitly interpreted by `π₂:V×2→2`. This operation is precisely what the proof requires: valuation of `∀y φ` equals valuation of `φ`; together with substitution invariance this makes instantiation valid, while the quantifier-distribution axiom becomes its Boolean tautology. Generalization preserves truth. The neighboring argument therefore still constructs the consistent complete extension from a separator. No further correction is indicated by this pass.

(D) Cross-section consistency failures

The prior equality-convention discrepancy is resolved. At `appendices/b-three-point-cosheaves.tex:568–571`, decidable equality is the true fiber, as in Appendix A. At lines 591–597, equal endpoint values therefore give the second/true summand; naturality forces the unequal source pair into the same true fiber and yields the contradiction. The revision changes both the convention and its use consistently. Neither of Proposition B.10’s conclusions changes.

The deletion at `sections/04-theory-extensions.tex:242–244` removes only repetition after Theorem 5.3. The remaining claim about infinite c.e. carriers follows from duplicate-free enumeration and inverse search; it is not used to replace the theorem’s sentence and theory data.

The unchanged Lemma 5.1 was rechecked at its critical quantifiers. For any slice object `p:X→T`, an underlying partial computation `f:X×Q⇀Q` admits a total code `a:X→Q`; the slice parameter is `⟨p,a⟩:X→T×Q`. For objects `T×X→T` of the full recursion subcategory, the parameter may depend on both coordinates. The proof makes no unsupported demand for a parameter constant over T. A total mono `⟨p,m_X⟩` and its assumed partial inverse give the required restriction retract.

(E) Acceptance conditions, non-negotiable

No new repair condition is raised by this repeat review. Retain the explicit projection and true-fiber convention when integrating the revision. Preserve the previously open Lean obligations; this review does not discharge them.

(F) Not checked / uncertainty log

- No fresh Lean build or transitive axiom audit was run.
- This repeat pass checked every changed core passage and its surrounding proof, compared all assigned numbered statements literally, and reused the previously recorded proof reconstructions only after confirming unchanged source. It did not rerun the complete 77-proof audit.
- Application proofs outside this scope remain assigned to the other reviewers.
- Bibliographic attributions were not independently reauthenticated.
- KLR consultation remains the honestly recorded partial scope from the earlier core audit; the separate writing reviewer has the full-manual assignment. No claim of complete KLR reading is made here.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none remaining in the assigned passages. Most important unchecked item: full current Lean correspondence and the other application scopes. The scoped conclusion does not depend on missing material; whole-paper acceptance does. Final recommendation: **unknown** for the whole paper; no rejection condition arises from this repeat core review.
