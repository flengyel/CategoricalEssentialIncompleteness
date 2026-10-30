# (A) Kill-shots / hard blockers

Date: 29 October 2026. This is an author-side mathematical audit of the
complete `OTHER_THEORIES.md` in this directory. The genre is a research
record extending an existing construction, not a journal submission.
The audit addresses correctness, typing, attribution, and the scope of the
claimed applications. It makes no novelty or publication recommendation.

No fatal defect is confirmed in the displayed arguments. The scope is
relative to theories admitting the stated presentations or translations.
The record does not infer that every recursion category supplies one.

# (B) Major weaknesses

No major defect is confirmed. The following checks record the mathematical
content reviewed and the hypotheses on which each conclusion depends.

| Anchor and claim | Evidence and reconstruction | Status |
| --- | --- | --- |
| §1, relative existence theorem | Derivation: if a separator contains `I_T` and avoids `Z_T`, the inclusions `I_B≤I_T` and `Z_B≤Z_T` make it a separator of the base pair. Completeness is separately required to supply such a computational separator. Existence of an arbitrary relation is not substituted for these data. | Checked. |
| §2, `T^theta` is c.e. | Derivation: enumerate arithmetic sentences and T-proofs in parallel, comparing each translated sentence with proof conclusions. A computable inverse to the translation is unnecessary. Effectiveness of the language, translation, and proof enumeration is used here. | Checked. |
| §2, `T^theta` is a classical theory extending PA | Derivation: translated PA theorems give inclusion. A finite classical deduction from sentences in `T^theta` translates to a deduction from their T-provable translations, giving closure. The assumptions explicitly concern deductions from premises, not only PA theorems. | Checked. |
| §2, consistency and completeness transfer | Derivation: falsum in `T^theta` yields translated falsum in T, and the falsum clause yields inconsistency of T. If T decides `phi^theta`, the negation clause converts a proof of its negation into membership of `not-phi` in `T^theta`. Soundness and standard-model correctness are not used. | Checked. |
| §2, category `S_{T,theta}` | Structural argument: the established unprimed construction is applied to the actual consistent c.e. arithmetic theory `T^theta`. Equality is one T-proof of the translation of the uniformly quantified equation. No pointwise-provability quotient or new composition law is asserted. | Checked against the prior construction record. |
| §2, extension functor | Derivation: inclusion of target theories gives inclusion of inverse-image theories. The object map is identity on the formal numerical types; the arrow map retains a program representative while passing to the larger equality quotient. This is well-defined, preserves the fixed operations, and satisfies identity and composition literally on representatives. The walking-arrow test has the asserted direction only. | Checked. |
| §2, source category and functor into `Cat` | Derivation: objects are pairs `(T,theta)`, and arrows are actual effective deduction-preserving sentence functions j with the displayed compatibility and preservation of provable equivalence. For composable j,k, the latter property carries the first compatibility equivalence through k, and transitivity with the second compatibility gives compatibility of their composite. Identity and composition of the functions give a category. A T-proof of `phi^theta` then yields a T'-proof of `phi^{theta'}`, giving the theory inclusion. The induced quotient functors compose literally on the unchanged representatives. | Checked. |
| §3(1), `ACA_0` | Primary-source check: Simpson, Remark I.3.3, states the conservation of `ACA_0` over first-order PA and gives the model-expansion argument. With the inclusion translation this yields exactly `PA`, so the constructed base category is `S_PA`. Effective deduction is distinguished from full second-order semantic consequence. | Checked. |
| §3(2), finite set theory | Primary-source check: Kaye–Wong §3 defines precisely `EST + Pow + Found + not-Inf`; EST has the six listed axioms/schemes. Definition 7 and Theorem 8 give the ordinal interpretation `o:PA→ZF_{-inf}`. The note uses this direction only and correctly declines to infer an inverse interpretation without further hypotheses. | Checked. |
| §3(3), negative translation | Primary-source check and derivation: Avigad–Feferman Theorem 2.1.1 translates classical deductions from arbitrary premises, and Corollary 2.1.2 gives `PA⊢phi ⇒ HA⊢phi^N`. The displayed clauses preserve conjunction and implication; negation and falsum commute up to intuitionistically provable equivalence. These are exactly the hypotheses used in §2. | Checked. |
| §3(3), `HA^N=PA` | Derivation: negative translation gives the forward inclusion of PA. If HA proves `phi^N`, then PA proves it, and classical equivalence of `phi^N` with `phi` gives the reverse inclusion. For a stronger intuitionistic T the inverse image may be a larger classical theory. Completeness is explicitly sentence-by-sentence decidability, not the excluded-middle schema. | Checked. |
| §4, categorical precompleteness formula | Type check: `psi:X⇀P`, `h:X→P` total, and `rho:P²⇀P²` a restriction idempotent give `rho<psi,h>:X⇀P²`; its restriction and `bar(psi)` are both endomorphisms of X. The pairing already has restriction `bar(psi)`. Thus the equation asserts exactly totalization modulo the relation on the defined inputs. | Checked. |
| §4, upward closure | Derivation: `rho≤rho'` gives a lower bound on the restriction after composing with the same partial pairing; composition gives the upper bound `bar(psi)`. Equality for rho therefore gives equality for rho'. The larger domain is required still to be an equivalence relation. | Checked. |
| §4, distinct-class inseparability lemma | Derivation: dovetail the two disjoint c.e. input domains and return the two fixed representatives on the corresponding branches. Precompleteness gives a total recursive map sending each input domain into its assigned class. A recursive separator pulls back along that map, contradicting the fixed input pair's inseparability. C.e.-ness of the classes is asserted only with the additional c.e. relation hypothesis. | Checked. |
| §4, PA program equivalence is precomplete | Derivation: the parameter theorem represents the family that first obtains the output index from the partial computation and then runs that program. A genuine terminating first computation has a PA-verifiable finite trace. Together with the PA-verified program specification, that proof yields uniform equality of the represented output program with the returned program. Only convergent inputs are constrained by precompleteness. | Checked. |
| §4, arithmetic sentence equivalence warning | Primary-source check: Barendregt–Terwijn §2 distinguishes PA's full Lindenbaum equivalence from the program examples. Negation has no fixed point modulo provable equivalence in a consistent theory, whereas precomplete numberings satisfy the stated fixed-point theorem. This is not a claim about an inconsistent theory. | Checked. |
| §5, lambda-theory equivalence | Primary-source check: Barendregt–Terwijn §2 supplies precompleteness of closed lambda terms modulo beta equality. Enlarging to the equivalence relation of a lambda theory preserves precompleteness by the already-proved law. Effective syntax and c.e. deduction make the relation and its fixed classes c.e. | Checked. |
| §5, distinct `K` and `K_*` classes | Derivation: equality of these two closed terms, followed by congruence under application to arbitrary M,N and beta conversion, gives M=N. Thus consistency of the lambda theory keeps the classes distinct. The note does not identify these terms with categorical identity and zero. | Checked. |
| §5, no maximal consistent c.e. lambda theory | Derivation: the two searches concern respectively `T⊢M=K` and collapse of the one-equation extension. Both are effective. If the first succeeds, adjoining the equation changes no theorems, so the second would contradict consistency. If the first never succeeds, maximality forces the proper extension to collapse, so the second succeeds. This decides the K-class, contradicting its established inseparability. No negation connective is assumed. | Checked. |
| §5, a proper consistent c.e. one-equation extension exists | Derivation: if every closed equation `M=K` not already provable caused collapse, the same two searches would decide the K-class. Hence some such equation is neither provable nor collapse-producing. Adjoining that single equation is proper, consistent, and remains c.e. | Checked. |

The categorical assertions in §§2–3 reuse the existing verification of the
valid unprimed construction; the numerical precompleteness and lambda
arguments in §§4–5 are reconstructed explicitly. Neither route treats an
ordinary subobject of a larger category as automatically computational.

# (C) Minor issues

No confirmed minor mathematical defect remains in the reviewed text.

Two limitations are correctly stated and must remain: the stronger
Bernardi theorem is not transferred to nondominical categories, and the
lambda example is an application in classical `Rec`, not a claimed new
Heller recursion category constructed from a lambda theory. These are
scope boundaries, not defects in the propositions actually proved.

# (D) Cross-section consistency failures

No unresolved framework drift is confirmed.

- The arithmetic translations produce actual classical theories before
  the existing `S_B` construction is applied. The intuitionistic target
  does not require an unproved direct construction of a category from
  intuitionistic derivability.
- The negative translation is treated as an effective proof translation,
  separately from ordinary relative interpretations. Its use does not
  claim that it is an ordinary homomorphic first-order interpretation.
- The source category uses actual translation functions rather than an
  unstated quotient of interpretations. Preservation of provable
  equivalence is explicit and is precisely what makes the displayed
  compatibility condition stable under composition. The target is `Cat`;
  no fullness, faithfulness, or recovery of the whole target theory is
  asserted.
- Categorical functors go from the earlier quotient category to the later
  quotient category. The backwards operation is pullback of separators
  along the resulting pair reductions.
- Precompleteness constrains a total representative only where the given
  partial map is defined. The argument never asserts a total extension
  with literal equality on codes, or a fixed result on divergent inputs.
- The relation for program equations and the relation for arbitrary
  arithmetic sentences are explicitly distinguished.
- The numerical distinct-class lemma requires no unverified extension of
  Bernardi's dominical theorem. Its proof uses ordinary partial recursive
  dovetailing and a total recursive reduction.
- The lambda conclusion concerns maximal consistent equational theories.
  It does not substitute excluded middle, or a nonexistent term-negation
  operation, for the effective inconsistency search in the extension.
- None of the applications asserts intrinsically nonnumerical
  computability. Their actual computational ambient category is stated.

# (E) Acceptance conditions, non-negotiable

1. **Keep the premise-translation and negation clauses.** Deliverable: §2.
   Endpoint: the proof that `T^theta` is a classical theory and inherits
   hypothetical completeness must use these exact clauses. Status: met.
   Without them, the proposition must be narrowed or withdrawn.
2. **Retain the valid uniform quotient.** Deliverable: §2 and its link to
   the prior source record. Endpoint: one proof of the translated uniform
   equality sentence, followed by the established `S_B` construction.
   Status: met. A pointwise replacement would invalidate this application.
3. **Keep the finite set theory and interpretation direction exact.**
   Deliverable: §3(2). Endpoint: the stated EST axioms, Pow, Found,
   not-Infinity, and the ordinal map from PA. Status: met. Unsupported
   inverse or bi-interpretation claims would have to be removed.
4. **Preserve the precompleteness typing and scope.** Deliverable: §4.
   Endpoint: total h, partial psi, the correctly typed restriction
   equation, and separate c.e.-ness where computational domains are used.
   Status: met. A stronger dominical application needs its own hypothesis
   verification and cannot replace the numerical proof.
5. **Keep both lambda searches and the meaning of collapse explicit.**
   Deliverable: §5. Endpoint: effective search for equality versus proof
   of `K=K_*` in the one-equation extension, with exclusivity and coverage
   derived from consistency and maximality. Status: met. Without this
   argument the maximality conclusion would be unproved.
6. **Retain the declared computational ambient category.** Deliverable:
   §§3 and 5 and the final scope paragraph. Endpoint: no claim of a new
   nonnumerical recursion category is attached to these examples.
   Status: met. Such a stronger claim would require a separate construction.

# (F) Not checked / uncertainty log

- The entire new note was read. The inverse-image theory proposition,
  induced quotient maps, numerical inseparability lemma, PA
  precompleteness argument, and lambda maximality proof were reconstructed
  from the stated hypotheses.
- The final explicit source-category definition, separator definition,
  deductive-closure convention for theories, and definition of `R_PA`
  were reread after the local typing edits. The inspected file has SHA-256
  `0fc1c4248cefb5d2acb231c1f7a17ef211a0df01ae6e5f787cff89474063ae15`.
- Independently inspected primary PDF text: Barendregt–Terwijn §2 and the
  fixed-point statement in §3; Avigad–Feferman §2.1; Kaye–Wong §§2–4;
  Simpson Remark I.3.3. Their formulas and relevant attributions support
  the applications recorded above.
- Independently inspected Bernardi's author-uploaded extracted text:
  the program-equivalence example on p.125; the recursion-category scope
  at the start of §3; Definition 1 and its upward-closure observation;
  and Theorem 2 with its c-plus-dominical hypothesis. The publisher scan
  remains unavailable. OCR alone is not treated as verification of the
  stronger theorem's complete proof. That theorem is not needed by any
  numerical application established here.
- The existing construction of unprimed `S_B` and its fixed program
  specifications were not audited from scratch again. Their prior
  verification is explicitly reused. No primed construction is imported.
- No weak-base construction for PRA, I-Sigma_1, RCA_0, or Q is certified.
  The record expressly leaves those outside the checked examples.
- No Lean development was run, and no new formalization is claimed.

Strongest confirmed blocker: none for the displayed applications.
Strongest suspected unconfirmed blocker: none identified in those proofs.
Most important item not checked: the complete scanned proof of Bernardi's
stronger categorical inseparability theorem and applications beyond the
stated numerical presentations.
Dependence on unavailable material: none for the reconstructed numerical
and interpretation arguments; the stronger Bernardi result remains an
attribution with the stated source limitation.
Final recommendation: **unknown** for any broader categorical generalization;
no confirmed mathematical blocker remains for the propositions audited here.
