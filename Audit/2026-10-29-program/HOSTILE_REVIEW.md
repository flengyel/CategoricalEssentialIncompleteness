# (A) Kill-shots / hard blockers

**Verdict:** the note proves a conditional categorical inseparability theorem and an arithmetic specialization. It does **not establish the stronger claim that the developed deduction, presentation, and recursion machinery are integrated in the incompleteness proof**. The decisive evidence is a deletion argument: the proof of Theorem 4.2 does not use closure or the Turing morphism; Theorem 4.3 does not use closedness of the extension. This defeats the stated requirement that those ingredients do mathematical work in the obstruction. It does not refute the conditional theorems.

This is an author-side adversarial audit of *Deduction and essential incompleteness in recursion categories*, dated 29 October 2026. The outline supplied for this review is `OUTLINE.md`; the reviewed starting version is commit `a9da9ee538edbf4a57e4469185f014aa88c5daf8`. All nine pages and the complete LaTeX source were read. Page references below refer to that version. The only subsequent manuscript change considered here is the abstract qualification recorded in section (D).

No theorem-breaking counterexample was established. In particular, the following attempted objections fail:

- **A diagonal is not disqualifying.** Di Paola–Heller explicitly seek generalized diagonalizations expressed in recursion theorems (1987, p. 596), and their Theorem 8.15 uses a diagonal.
- **A representation hypothesis is not itself circular.** Their stated goal includes the implication from definability of recursive sets to recursive inseparability (pp. 594–595, item (3)). Definition 4.1 is a plausible algebraic counterpart of that antecedent; the note proves the ensuing obstruction rather than assuming it.
- **Unused Turing universality does not prove that the result is merely set theory.** The ambient morphism and domain classes matter. In the category of all partial set maps, every disjoint pair of domains below $s$ has the separator $(p_+,s\setminus p_+)$. Consequently the note's nontrivial representation condition cannot hold there. In the numerical recursion category the allowed domains are c.e., so the complement used in that argument need not be a morphism.
- **Effective inseparability and Kelly enrichment are not prerequisites for every version of the announced program.** Di Paola–Heller list several alternative generalized incompleteness statements. Their Definition 8.17 adds uniform index data absent from this note, but this does not invalidate the note's weaker recursive-inseparability conclusion. The original program does not prescribe a Kelly-enriched category.

The assessment must therefore distinguish two claims: an algebraic analogue of one implication listed by Di Paola–Heller is present; fulfillment of the stronger intrinsic construction sought in this project remains unestablished.

# (B) Major weaknesses

## B1. Deductive closure and the presentation category do not drive the incompleteness argument

**Anchor:** p. 6, Theorem 4.2, “a closure $c_s:E_s\to E_s$”; pp. 6–7, Theorem 4.3, “a presentation satisfy the deduction-chain hypotheses”; p. 5, §3.1, “The inclusions form a natural transformation.”

**Claim as written:** Theorem 4.3 concerns closed theories from the constructed presentation. The stronger claim under examination is that the machinery of deduction and presentations is used to obtain their essential incompleteness. That stronger claim is the review target; the note does not explicitly assert that every preceding construction is indispensable.

**Failure mode:** `unused_hypothesis` for the obstruction proof; `unsupported_generalization` if that proof is presented as establishing the stronger integration claim.

**Why it fails:** Theorem 4.2 works for any disjoint domains $p_+,p_-\le s$ satisfying the two representation equations, without a closure operator and without an equation $p_-=\nu^*p_+$. Its proof uses total inverse image, products, complementation, and representation. Theorem 4.3 then excludes any complete consistent domain extension $t\ge b$, whether or not $t$ is closed. Neither proof uses a rule morphism, a deduction stage, a chain union, a morphism of $\mathsf{Cons}$, or the reflector.

**Evidence:** `structural_argument` and `derivation`. Replace $b,b^-$ by $p_+,p_-$ throughout Theorem 4.2. The same $\delta=\sigma\Delta$, $\gamma=\langle1,g\rangle$, and $h=\delta g$ give $h^*p_+=h^*d_-$ and $h^*p_-=h^*d_+$. The separator inclusions force equal complementary domains and hence $0_U=1_U$. For Theorem 4.3 only $b\le t$, monotonicity of $\nu^*$, and the consistency/completeness equations remain.

One can also take $q=s$, $\ell=0$, and the single unary rule $r=s$. Every stage is $a$, every domain below $s$ is closed, and the same obstruction proof applies whenever representation holds. No nontrivial deductive operation is needed for that argument.

**Missing ingredient:** a theorem explaining which deduction or translation properties are required to establish or transport the representation condition, rather than merely selecting a subclass of domains after the obstruction has already been proved.

**Downstream impact:** ranges and stable unions genuinely construct closure, but the inferential connection between that construction and essential incompleteness is weaker than the project's stated requirement. The existence of a valid stronger domain theorem is not a mathematical defect; describing the closure construction as indispensable would be inaccurate.

**Severity:** major for the stronger integration claim; not a correctness objection to Theorems 3.1, 4.2, or 4.3. **Repairability:** requires an additional substantive linkage theorem, or a narrower account of the role of the closure construction.

## B2. The intrinsic formal-system/recursion comparison is not supplied

**Anchor:** p. 2, §1, “The intended examples are recursion categories”; p. 6, §4, “Supply a morphism” and Definition 4.1; pp. 8–9, §5.2, “Choose a total computable enumeration” and the numeralwise-definability hypothesis. Primary comparison: Di Paola–Heller (1987), pp. 594–596 and Theorem 8.15, pp. 625–626.

**Claim as written:** the note supplies rule morphisms, $\nu$, $\sigma$, and a representation condition in an ambient partial-map category; in arithmetic it realizes these data with external effective syntax. The stronger assertion tested here is that this completes the intrinsic algebraic treatment contemplated by Di Paola–Heller.

**Failure mode:** `unproved` and `unsupported_generalization` for that stronger assertion.

**Why it fails:** there is no construction from a specified algebraic structure for formal systems to the relevant dominical or recursion category, and no comparison showing how such a structure gives the representation data. Conversely, the note does not derive a structure of definable predicates and its logical operations from a recursion category or a completion. The domain functor $E$ is a functor of computational domains; it is not accompanied by a general construction of formula definability. The numerical section verifies the intended interpretation under a syntactic definability assumption, but is the only exhibited realization.

**Evidence:** `absence_in_text`, `structural_argument`, and `citation`. The Turing morphism is declared in §1 and mentioned in §5, but no subsequent equation invokes its universal property to construct logical data or prove representation. Di Paola–Heller, p. 596, distinguish an intrinsic development compatible with algebraic formal systems from an external recursion theory inserted into them. Their Theorem 8.15 constructs an inseparable pair from a Turing morphism. The note neither uses that construction nor supplies a comparison with it. The supplied primary-source dossier records the precise scope of their stated goal.

**Missing ingredient:** a typed construction or comparison between a specified algebraic account of formal systems and the computational category carrying its deduction and representation data. It need not use polyadic algebras, and it need not derive strong representability from recursion-category axioms alone: strong representability is an additional logical-strength hypothesis in the original arithmetic statements as well.

**Downstream impact:** the claim that the full intrinsic program has been completed is unsupported. This finding does not show that the current theorem fails to approximate Di Paola–Heller's item (3), nor that another categorical realization cannot be built.

**Severity:** major for full program fulfillment. **Repairability:** requires a mathematical construction or comparison, not a renamed definition or an added historical claim.

## B3. $\mathsf{Cons}$ does not encode the structures whose consistency and completeness are later studied

**Anchor:** p. 5, §3.1, presentation data “$(U,q,s,\ell,(r_i))$”; p. 6, §4, $t^-=\nu^*t$ and the consistency/completeness definitions.

**Claim as written:** $\mathsf{Cons}$ organizes deduction presentations and their closed domains. It does not claim to preserve the later negative operation or representation condition. Nevertheless, it cannot serve as the category of the complete structures of §4 without further data and conditions.

**Failure mode:** `missing_definition` for the proposed stronger category of logical structures; no failure of the stated category laws.

**Evidence:** `counterexample` to preservation of consistency by the existing presentation data. In $\mathscr R_{\mathrm{rec}}$, take $U=\mathbb N$, $q=s=1_U$, $\ell=0$, and the unary identity rule. Then $c_s=1_{E_s}$. Let $t$ be the partial identity on the even numbers. With the total morphism $\nu_1(n)=n+1$, $t^-$ is the partial identity on the odd numbers, so $t$ is consistent and complete. With $\nu_2(n)=n$, $t^-=t$, so $t$ is inconsistent and incomplete. Both morphisms satisfy the support equations in §4. The underlying object and identity arrow of $\mathsf{Cons}$ are the same in both cases because $\nu$ is not part of a presentation. No representation condition is asserted for this example, so it is not a counterexample to either incompleteness theorem. Minimality is not claimed.

**Why it matters:** the theory functor is genuinely functorial for closure, but the note has not extended that functorial account to the additional logical structure used in §4. In particular, preservation of $\nu$ and a suitable transport law for $\sigma$ and representatives are absent.

**Missing ingredient:** if translations are meant to transport the §4 structures, include those data and state and prove the required compatibility laws. The example does not justify adding arbitrary laws without checking the arithmetic interpretation.

**Downstream impact:** the presentation-category machinery cannot currently justify claims about functorial transport of representation, consistency, or incompleteness. **Severity:** major for that proposed role, not for the narrower closure theory. **Repairability:** extend the relevant category and prove transport results, or keep its stated role restricted to deductive closure.

# (C) Minor issues

**C1. Terminology comparison with the primary source is absent.** Anchor: p. 6, §4, “computationally inseparable”; Di Paola–Heller, Definition 8.14, p. 625. Failure mode: `ambiguous` only for an asserted identification with that source. Evidence: `derivation`. The note excludes separators complementary relative to $s$; the primary source discusses complemented domains on the ambient object. The needed implication is elementary: an ambient separator $e_+,e_-$ restricts to $se_+,se_-$, which is complementary relative to $s$. Thus the note's conclusion implies ambient recursive inseparability. The reverse implication needs additional discussion and should not be asserted automatically. Downstream impact: no problem for the direction needed here, but a precise comparison would clarify the relationship. Severity: minor; repairable by stating the implication. Do not identify this with *effective* inseparability, which requires the uniform index data of Definition 8.17.

No claim of novelty was found, and no novelty failure is alleged. The absence of a nonnumerical example is a limitation of demonstrated scope, not a counterexample to the theorem or a proof that such examples cannot exist. Similarly, §5.1 realizes the closure for $Q$ and PA, but does not prove their separate numeralwise-representability theorems. The note's conditional corollary does not purport to prove those theorems.

# (D) Cross-section consistency failures

**D1. Abstract versus Corollary 5.2 — resolved during this review.** Anchor: p. 1, abstract, originally “essential incompleteness for every consistent theory strongly defining all recursive sets numeralwise”; p. 9, Corollary 5.2. Failure mode: `ambiguous`. The abstract omitted the c.e. qualification on the extensions. Evidence: `absence_in_text` compared with the corollary's explicit quantifiers. The replacement now states: “In the arithmetic instance, every consistent computably enumerable extension of a consistent theory strongly defining all recursive sets numeralwise is incomplete; the base theory need not be computably enumerable.” Downstream impact: the abstract now matches the theorem. Original severity: minor exposition issue with a potentially substantial scope misreading; repair completed without changing the mathematics.

The remaining central definitions and results were checked as follows. “No failure found” is a source-level assessment of the stated implication, not proof-assistant verification.

| Anchor | Typed claim, hypotheses, and principal check | Status |
|---|---|---|
| Definition 1.1; Lemma 1.2, p. 2 | Universal range $\operatorname{ran}(f)\in\operatorname{Dom}(Y)$ for $f:X\to Y$. Use parallel-arrow agreement to prove leastness and uniqueness; compose receiving and agreement equations for the composition and restriction identities. | No failure found. |
| $E_!:\mathscr R\to\mathbf{Pos}$, p. 2 | $f_!(e)=\operatorname{ran}(fe)$. Domain-range and composition identities give identity and composition laws. For partial $f$, the adjunction formula correctly retains $e\bar f$. | No failure found. |
| Definition 2.1; Lemma 2.2, p. 3 | Stable union is universal agreement plus product stability. Fixed-domain multiplication and direct image preserve union; the graph range and projection prove preservation by total inverse image, including output stability. | No failure found. |
| $E:\operatorname{Tot}(\mathscr R)^{op}\to\mathbf{BDLat}$, p. 3 | $f^{op}\mapsto f^*$; totality gives preservation of top, restriction zeros of bottom, and Lemma 2.2 of joins. On an arrow $A\to B$, the direction is $E(B)\to E(A)$; no reverse arrow is assumed. | No variance or functor-law failure found. |
| Lemma 2.3, p. 4 | For a stable increasing-chain union, finite products reduce mixed indices to their maximum and then use stability one coordinate at a time. Parameter factor is retained. | No failure found. |
| Theorem 3.1, p. 4 | Supported finite-arity rules, ranges, finite stable unions, and stable unions of generated chains. Products and direct image preserve those unions; induction proves leastness, then extensivity, monotonicity, idempotence. | Hypotheses genuinely construct closure. |
| $c_s,L\dashv i$, p. 5 | $c_s(a)=s c_q(a)$ on $E_s$; monotonicity bounds the double application by $c_s(a)$, and extensivity supplies the reverse. For closed $t$, $c_s(a)\le t\iff a\le t$. | No failure found. |
| $\mathsf{Cons},\mathsf{Th},\mathcal E,i$, p. 5 | Supported arrows satisfy $c_s f^*\le f^*c_{s'}$. Supports and inequalities compose. Inverse image sends fixed points to fixed points. Naturality is $\mathcal E(f^{op})i_{P'}=i_P\mathsf{Th}(f^{op})$, since both maps send $t$ to $f^*t$. | Correct for closure data; B3 limits its larger role. |
| Definition 4.1; Theorem 4.2, p. 6 | Nontrivial $U$, total supported $\sigma$, disjoint positive/negative domains, and the two representation equations. Diagonal pullback reverses a purported separator; representation gives equal complementary pullbacks. | No failure found; closure and Turing universality unused. |
| Theorem 4.3 and inheritance, pp. 6–7 | Monotonic $\nu^*$ sends $b\le t$ to $b^-\le t^-$. Completeness gives a separator. For inheritance, disjoint extensions of complementary lower bounds equal those bounds by distributivity. | No failure found; closedness unused in the obstruction. |
| Proposition 5.1 and counterexample, p. 7 | Uniformly c.e. family gives a c.e. tagged domain and projected range; pointwise agreement, including definedness, proves stable union. Finite approximations to a non-c.e. set exclude arbitrary increasing unions. | No failure found; uniformity is not confused with arbitrary countable joins. |
| Effective deduction, p. 8 | Modus ponens and parameterized generalization are partial recursive maps. Recursive index transformation gives uniform stages; induction on finite proof height identifies the union with derivability from sentence axioms. | No failure found at the mathematical algorithm level. |
| Representation, pp. 8–9 | Jointly total recursive numeral substitution; strong numeralwise definitions plus consistency give exact positive/negative preimages. Constant $g$ is total and realizes the representation equations. | No failure found; arithmetic strong definability is an explicit premise. |
| Corollary 5.2, p. 9 | Transfer definitions from possibly non-c.e. $B$ to each consistent c.e. $T$; apply the categorical theorem to the theorem domain of $T$. | Valid transfer argument; no domain for $B$ is needed. |

The previous audit's source-level conclusion that the conditional proofs had no confirmed blocker is not contradicted by B1–B3. That audit expressly did not certify complete fulfillment of the historical program. The present review tests that additional claim and the project's stronger integration requirement.

# (E) Acceptance conditions, non-negotiable

These conditions govern a claim of **full intrinsic program fulfillment**, not permission to retain the conditional mathematical results.

1. **Deliver a precise scope statement.** Separate the proved analogue of recursive-set definability implying inseparability from the stronger intrinsic construction. Endpoint: the claimed achievement matches a stated result and its verified interpretation. Relevant sections: introduction, §4, §5. Failure requires rejection of the full-fulfillment claim.
2. **Deliver the missing intrinsic comparison.** Specify the algebraic formal-system objects, their morphisms, the computational category associated with or supporting them, and the logical/representation data. Prove the relevant typing, functorial or structural laws and arithmetic interpretation. Endpoint: the relation between formal-system structure and recursion structure can be checked independently of a declaration that the representation equations hold. Relevant sections: §§3–5. Failure requires dropping the stronger intrinsic-construction claim; it does not invalidate the existing conditional theorem.
3. **Account for the role of closure.** If the project requires the developed deductive machinery to enter the incompleteness proof, prove how it establishes or transports the decisive representation property. Endpoint: a dependency in the proof uses a stated property of rules, closure, or theory translation. Alternatively, state that closure only identifies the intended class of theories. Relevant results: Theorems 3.1 and 4.2–4.3. Failure rejects the claim that all this machinery drives the obstruction.
4. **Define transport for the full §4 structures if functorial transport is claimed.** Include the necessary $\nu,\sigma$ data and prove preservation of the properties actually asserted. Endpoint: the two expansions in B3 are distinguished, and the proposed laws are verified in the arithmetic instance. Relevant section: §3.1 and §4. Failure requires dropping any assertion that the current $\mathsf{Cons}$ already supplies that account.
5. **Keep inseparability claims at their proved strength.** State the relation between relative separators and Di Paola–Heller's ambient separators. Any claim of effective inseparability must additionally exhibit the uniform morphism and index laws of that notion. Endpoint: an explicit implication/comparison with the cited definition. Relevant section: §4. Failure requires dropping any unproved identification or strengthening; the current recursive-inseparability result can remain.

# (F) Not checked / uncertainty log

- Primary-source consultation covered Di Paola–Heller's introduction, printed pp. 594–596, and Definitions/Theorems 8.14–8.18, pp. 625–627, in the supplied original paper. These establish the historical distinction used here. The entire 42-page article was not re-audited. No demand that every recursion-category axiom appear in every proof is attributed to that source.
- Heller's original stable-union development was not independently rechecked in this audit. The note's stated universal definition and the arguments using it were checked. No additional product-range hypothesis was found necessary for the graph proof as written.
- The note contains no Lean implementation of the new constructions. No Lean build, axiom audit, executable arithmetic coding test, or novelty search was performed by this reviewer. The parent handled the limited prose edit and compilation.
- No proof was found that all possible future versions of this approach fail the Di Paola–Heller program. The absence of the intrinsic comparison is evidence of an unproved achievement claim, not an impossibility theorem.
- The primary source allows an algebraic approximation to any one of several incompleteness statements. Accordingly, the narrower claim that this note supplies a categorical version of its item (3) remains plausible and is supported by the displayed theorem and arithmetic interpretation. The review has not refuted that claim.

**Final self-audit.** Strongest confirmed blocker: the stronger requirement that deduction, presentation morphisms, and Turing universality participate in the obstruction is not met by the displayed proof; B1 gives the deletion argument. Strongest suspected but unconfirmed blocker: that the missing intrinsic comparison cannot be supplied without replacing the representation framework; no impossibility result has been established. Most important unchecked item: a general mathematical construction relating an algebraic account of formal systems to the recursion-category and representation data. The negative assessment of the stronger claim depends on the current note's contents, not on unavailable material. **Final recommendation: reject unless major reconstruction, as a claim of completed intrinsic program fulfillment with the stated integration requirement; no rejection of the conditional theorems follows from this audit.**
