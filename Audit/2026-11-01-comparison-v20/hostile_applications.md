# Focused check of printed §§6–9, manuscript v20

Reviewed source: `output/manuscript/local_connectedness/sections/05-syntactic-recursion-category.tex`, `05a-internal-syntax.tex`, `06-interpretation-in-models.tex`, `07-faithful-family-and-theory-extension.tex`, and `08-essential-incompleteness-of-arithmetic.tex`. Printed section numbers differ from filename prefixes. The PDF is the 61-page v20 manuscript at commit `c182b1b2c54af499e0ef6f3f7ae6f179eaa55b65`. These files were read in full. This check does not independently verify their literature citations or certify every retained proof.

## Confirmed dependence

| Printed result | Anchor | Dependence in the written proof |
|---|---|---|
| Theorem 6.9: internal syntax and generated theories | p. 28; `05a-internal-syntax.tex`, lines 808–873 | Lemmas 6.2–6.3, parameterized syntax/list initiality, substitution realization, derivation initiality, and Appendix A's least-image and range/image results. Neither Theorem 3.1 nor Theorem 4.2 is used to construct these theory objects. |
| Proposition 7.1: interpretation in one model | p. 29; `06-interpretation-in-models.tex`, lines 31–56 | PA-provable graph laws interpreted in a fixed model of T. It constructs F_M and proves preservation of restrictions, ranges, products, coproducts, zeros, and joins. |
| Theorem 8.1: faithful family | pp. 29–30; `07-faithful-family-and-theory-extension.tex`, lines 24–56 | Proposition 7.1, completeness, and downward Löwenheim–Skolem; connected singleton coordinate domains establish local connectedness. |
| Corollary 8.3: inseparability in S_T and extensions | p. 31; same file, lines 136–160 | Theorem 8.1 and Lemma 8.2 verify the hypotheses of source-inseparability Theorem 3.5. Theorem 3.5 is now proved using Theorem 3.1. |
| Corollary 9.2: arithmetic | p. 34; `08-essential-incompleteness-of-arithmetic.tex`, lines 213–230 | Source-inseparability Theorem 3.5 supplies A,B; explicit computation-to-proof inclusions and source-consistency Corollary 4.3 supply theorem/refutation inseparability. |

None of these files refers to Proposition 4.1 or Theorem 4.2. The new comparison theorem therefore reaches the retained applications indirectly through Theorem 3.5, while the new semantic-consistency application in Theorem 4.2 remains abstract in v20. This is incomplete incorporation of the proposed new route, not evidence that either theorem is false. The user explicitly requested beginning the section revisions, so it is not a contradiction of the reported revision scope.

## Proof-object initiality check

The key concern was whether arbitrary axiom subobjects and arbitrary inference algebras require decidable membership or globally total programs. No such requirement was found in the proof as written.

In `05a-internal-syntax.tex`, lines 291–315 establish that finitely many Σ₁ membership conditions can be represented by one Σ₁ formula, using coded lists of witnesses and PA induction. Lines 637–805 apply this to a derivation carrier P(d). Membership witnesses are existentially quantified and are not components of the derivation code. Thus no decidable axiom predicate is silently assumed.

For an arbitrary algebra α:H(Q,q)→(Q,q), the evaluation relation E_a(d,y) is defined by finite node evaluation lists. T-induction on a valid derivation code gives evaluation values for the immediate children and the equations q(y_j)=c(d_j). Those equations place the assembled tuple in the specified domain of α. Its T-provable totality on that domain supplies the root value, and its slice equation supplies the conclusion equation. Full PA induction covers the arithmetic induction formula. Functional search for P(d)∧E_a(d,y) supplies the required program with exactly the source predicate as its domain. Uniqueness follows by the same induction from an arbitrary algebra-morphism equation. No confirmed gap was found in this argument.

## One-model interpretation and soundness

Proposition 7.1 does prove preservation of ranges. The trace predicates and intermediate witnesses range over the whole model M (lines 27–29). The interpreted coding γ_X^M:X_M→|M| is a bijection. Consequently interpreting R_e(y)≡∃x G_e(x,y) gives exactly the image of the interpreted partial function, as stated at lines 46–51. This is a direct image calculation, not an unsupported claim that F_M preserves existential quantification in an arbitrary category.

Proposition 7.1 does **not** prove soundness of the full interpreted derivation object. In particular it does not define a sentence-validity subobject or prove that the interpreted conclusion map factors through it. Such a conclusion would require a sound interpretation of the chosen axiom subobject A and the rules, including the treatment of nonstandard proof codes where relevant. Proposition 4.1 formulates the required factorization condition; it does not establish that condition automatically from the existence of F_M. No contrary claim was found in these files.

The faithful all-model family is stronger than what is needed merely to invoke source-inseparability Theorem 3.5: one fixed M⊨T gives a range functor into Pfn, and the proof of Lemma 8.2 verifies the conditional componentwise. Faithfulness is nevertheless used later in the standard-numeral observation equivalence in §9.1 (`08-essential-incompleteness-of-arithmetic.tex`, lines 260–282). Thus its placement may be reconsidered, but deleting the result without preserving that later dependence would be incorrect.

## Verdict and limits

No confirmed mathematical failure was found in the checked derivation initiality, model range preservation, or retained application implications. The concrete soundness/factorization and partial proof-search lift needed to instantiate Theorem 4.2 have not yet been written in these application sections. That is the principal remaining dependency for the proposed new route. Claims about the full future soundness construction or whole-paper correctness are outside this check.
