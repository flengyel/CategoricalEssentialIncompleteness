## (A) Kill-shots / hard blockers

None confirmed on the requested terminology, definition-order, and typing axes in baseline source lines 1908–2347. This is not a certification of the constructions' mathematical correctness.

## (B) Major weaknesses

### P07-1 — “split subfunctor” does not identify the category in which splitting occurs

- **Anchor:** PDF pp.24–25, Appendix B.2, baseline lines 1982–1984 and 2039–2043; earlier uses at lines 1265–1277. Quote: “Write $A,B\hookrightarrow V$ for their split subfunctors.”
- **Failure mode:** ambiguous; inconsistent_use.
- **Claim as written:** restriction idempotents $a,b$ have “split subfunctors,” and $t_0$ has a “split subfunctor.”
- **Failure:** the manuscript defines splitting a restriction idempotent in $\mathcal A$, but never defines “split subfunctor.” That expression can suggest a split monomorphism in the total category $\mathcal E$, which is different. The partial identities on c.e. subfunctors split in $\mathcal A$ without requiring their inclusions to have retractions in $\mathcal E$.
- **Evidence:** absence_in_text and structural_argument. A whole-source search finds the phrase but no definition. A total recursive retraction onto a nonrecursive c.e. subset would decide membership by testing whether the retraction fixes the input, so the total splitting cannot be inferred from the partial one.
- **Downstream impact:** ambiguity about the objects used to represent the atomic axioms and theorems.
- **Severity / repairability:** major expository ambiguity; local repair, no theorem alteration.
- **Repair:** “Let $A,B\subseteq V$ be the c.e.\ subfunctors on which $a,b$ are the partial identities.” At line 2041 use “The subfunctor through which $t_0$ splits is the least c.e.\ subfunctor ...” Apply the same wording to the earlier Section 8 occurrences. Do not add a defensive paragraph about total retractions; the explicit definition suffices.

## (C) Minor issues

### P07-2 — An unexplained geometric name remains in the syntax construction

- **Anchor:** PDF p.23, Appendix B.1, baseline lines 1933–1939. Quote: “so the fork $S=(S_1\xleftarrow{\sigma_1}S_0\xrightarrow{\sigma_2}S_2)$.”
- **Failure mode:** missing_definition (unnecessary local terminology).
- **Failure:** “fork” has not been defined as the particular functor used here. Its geometric shorthand contributes nothing once the indexing category is fixed.
- **Evidence:** absence_in_text; whole-source search finds no prose definition of “fork.” Internal LaTeX labels containing `fork` are not reader-facing terminology and need no change.
- **Downstream impact:** an avoidable extra name for an object of the already-defined functor category.
- **Severity / repairability:** minor; direct replacement.
- **Repair:** “These morphisms define the functor $S:J\to\mathcal C_{\mathrm{rec}}$ by $S(j)=S_j$ and $S(0\to i)=\sigma_i$.”

### P07-3 — “total natural map” should use the established morphism class

- **Anchors:** PDF pp.23–25, Appendix B.1–B.2, lines 1937–1939, 1953–1955, 2034–2036, and 2068–2069. Quotes: “total natural maps,” “a unique total natural map.”
- **Failure mode:** ambiguous.
- **Failure:** these arrows are morphisms of $\mathcal E$, whose morphisms have explicitly been defined as natural transformations. “Total” is relevant after passage to $\mathcal A$, but the expressions currently mix the terminology of the two categories without saying so.
- **Evidence:** citation within the manuscript: lines 1022–1025 define $\mathcal E$-morphisms; lines 1034–1045 define the partial-map category.
- **Downstream impact:** minor uncertainty about whether the universal property is asserted in $\mathcal E$ or among partial arrows.
- **Severity / repairability:** minor; terminological repair.
- **Repair:** use “natural transformations” or “morphisms of $\mathcal E$.” In Proposition B.1: “for every morphism $\alpha:P(Z)\to Z$ of $\mathcal E$, there is a unique morphism $u:S\to Z$ of $\mathcal E$ satisfying ...” The partial-category totality follows from the declared inclusion.

### P07-4 — “three restrictions” overloads the paper's restriction terminology

- **Anchor:** PDF p.24, Proposition B.1 proof, lines 1958–1965. Quote: “using the three restrictions of $\alpha_j$ ... at the corresponding tags.”
- **Failure mode:** ambiguous.
- **Failure:** the intended three operations are composites of $\alpha_j$ with the three coproduct injections; “restrictions” can instead suggest the restriction operation used throughout the paper.
- **Evidence:** structural_argument: the displayed source $V_j+Z_j+Z_j^2$ has precisely the three coproduct injections relevant to the recursive evaluation.
- **Downstream impact:** local ambiguity in the recursive definition of $u_j$.
- **Severity / repairability:** minor; one phrase.
- **Repair:** “using the composites of $\alpha_j:V_j+Z_j+Z_j^2\to Z_j$ with the three coproduct injections.” The following sentence “Every application ... has an input in its carrier” can be deleted; the ensuing induction states the needed result.

### P07-5 — “rule-closed” adds a redundant local adjective

- **Anchor:** PDF p.25, Theorem B.2 proof, lines 2062–2066. Quote: “Thus $T$ is rule-closed.”
- **Failure mode:** missing_definition (avoidable shorthand).
- **Failure:** the preceding sentence proves closure under one explicitly named rule, modus ponens. The new adjective is not needed and could be read as closure under a larger rule collection.
- **Evidence:** absence_in_text and local derivation; the manuscript gives no separate definition of “rule-closed.”
- **Downstream impact:** none beyond exposition.
- **Severity / repairability:** minor; replace with “Thus $T$ is closed under modus ponens.”

### P07-6 — Declare the halting notation at first use

- **Anchor:** PDF p.25, Appendix C opening, lines 2110–2114. Quote: “$K=\{e:\varphi_e(e)\mathord\downarrow\}$.”
- **Failure mode:** missing_definition.
- **Failure:** $\downarrow$ is standard recursion-theoretic notation, not idiosyncratic vocabulary, but its meaning is not explicitly declared before its first occurrence. The requested strict notation pass can remove this gap with one clause.
- **Evidence:** absence_in_text; whole-source search confirms this is the first use and no earlier convention is given.
- **Downstream impact:** interpretation of the set $K$.
- **Severity / repairability:** minor; local declaration.
- **Repair:** after introducing $(\varphi_e)$, write “Write $\varphi_e(x)\downarrow$ when this computation halts, and put ...” The later use of $\operatorname{dom}(\varphi_e)$ denotes its ordinary domain of definition and is standard.

### P07-7 — Explicit arrow signatures are omitted at the numerical Turing construction

- **Anchor:** PDF pp.26–27, Proposition C.1 proof, baseline lines 2193–2219. Quotes: “Define $\tau_K(\langle e,a\rangle,x)=f_{e,a}(x)$” and “$r(z)=\langle e(z),a(z)\rangle$ is total.”
- **Failure mode:** missing_definition (type signature, not the value formula).
- **Failure:** the formulas define the values, but the source and target of $\tau_K$ and $r$ are left to inference precisely where their Turing property is being established.
- **Evidence:** absence_in_text; no earlier typed declaration of these local maps occurs.
- **Downstream impact:** makes the types in $v=\tau_K(r\times1_\N)$ implicit.
- **Severity / repairability:** minor; direct typing.
- **Repair:** “Define $\tau_K:\N\times\N\rightharpoonup\N$ by ...”; later, “Thus the morphism $r:\N\to\N$ given by $r(z)=\langle e(z),a(z)\rangle$ is total in $\mathcal C_K$ ...”. The extension can be written $v_0:\N\times\N\rightharpoonup\N$ rather than reusing the capital letter $V$, which already denotes the nonnumerical universal object.

## (D) Cross-section consistency failures

The repeated “split subfunctor” and “total natural map” terminology should be repaired consistently at the earlier Section 8 occurrences as well as in Appendix B (P07-1 and P07-3). The one-letter reuse of $V$ for a numerical program at line 2202 is locally declared, so it is not an undefined symbol; replacing it by $v_0$ would preserve the earlier symbol's role and agree with the $f_0,g_0$ extension notation.

Confirmed adequate introduction and scope in the assigned range:

- $\mathcal E,J,\mathcal A,V,V_j,r_i^V$ are defined in Section 8 and recalled at the start of Appendix B; the local abbreviation $r_i=r_i^V$ is explicit.
- The grammar introduces $S_j,\theta_j,\nu_j,\Rightarrow_j$ before their use; $\sigma_i$, $P$ on objects and morphisms, and $\iota$ follow in that order.
- The initial-algebra property is stated explicitly, and the proof introduces the component maps $u_j$ and $z_i$ before use.
- $A_j,B_j$ precede positive and negative leaf labels. The three Hilbert schemes are displayed before proof trees refer to them. “Signed leaves” at line 2027 refers to the already-defined positive and negative leaves, so it is adequately introduced.
- $\mathrm{Prf}_j,c_j,\rho_i,\mathrm{Prf},c$ are constructed before the statement about $t_0=\operatorname{ran}(c)$.
- $K,W_a^K$, the pairing and its projections, $\mathcal C_K$, $D_f$, and $f_{e,a}$ precede their mathematical use. The meaning of $\simeq$ is explicitly restated at line 2142.
- $b,d,a_0,a_1,p,A,a_*,1_B,p_A,s_A$ are introduced in order. The domains denoted $D_f,D_{a_0},D_{a_1}$ are actual subsets of numerical source sets, not an illicit replacement of “restriction idempotent.”
- The words “ordinary” and “relative to $K$” distinguish two computability notions essential to the counterexample and should be retained.
- Bibliographic titles and author-supplied terminology are not candidates for mechanical replacement.

## (E) Acceptance conditions, non-negotiable

1. Replace “split subfunctor” with an explicit partial-identity/splitting description in Section 8 and Appendix B. Endpoint: no ambiguity between a splitting in $\mathcal A$ and a retraction in $\mathcal E$. Failure leaves the terminology review unresolved.
2. Replace the remaining “fork,” “total natural map,” and “three restrictions” prose in Appendix B with the corresponding typed functors, morphisms, and coproduct composites. Endpoint: the displayed constructions refer to the already-defined morphism classes. Failure leaves the requested terminology cleanup incomplete.
3. Declare the halting notation and the signatures of $\tau_K$ and $r$ before use. Endpoint: Appendix C's evaluator and parameterization equation have explicit types. Failure leaves the strict definition-order pass incomplete.
4. Preserve the class of arrows in $\mathcal C_K$, the distinction between ordinary and oracle computation, and the lifting counterexample. No mathematical hypothesis or conclusion needs to be weakened for these repairs.

## (F) Not checked / uncertainty log

Read every sentence, heading, displayed formula, proof paragraph, and bibliography entry in immutable baseline lines 1908–2347. The companion JSON records all assigned blocks B157–B188. Prior definitions were read in lines 1–295 and 979–1326; whole-source searches checked each absence claim. PDF page text was used for the cited page anchors. The governing mathematical-writing principles used are explicit variable introduction and consistent notation (Knuth–Larrabee–Roberts, Section 1, points 11 and 14) and reader-directed exposition (point 12), as available in the supplied excerpt; the requested vocabulary preference is an independent editorial constraint.

This pass did not repeat a correctness audit of every theorem or verify every bibliographic entry against external sources. No new bibliographic fact is asserted. The actual outline of this portion is Appendix B.1 (syntax and its initial algebra), B.2 (finite proofs, their range, and consistency), Appendix C (counterexample when lifting is omitted), then references; the dependencies in this order are appropriate.

Strongest confirmed blocker: P07-1, the ambiguous category of the alleged “split subfunctor,” is a repairable exposition defect, not a confirmed false theorem. Strongest suspected unconfirmed blocker: none identified within the requested scope. Most important thing not checked: independent correctness of the entire mathematical argument. Recommendation does not depend on unavailable source material for these editorial findings. Final recommendation: **unknown** as to mathematical acceptance; complete the stated repairs before accepting the terminology pass.
