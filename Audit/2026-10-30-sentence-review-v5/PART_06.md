## (A) Kill-shots / hard blockers

No fatal mathematical blocker was established by this terminology and definition-order review. This report does not certify the mathematical claims.

## (B) Major weaknesses

No major mathematical defect was established. The confirmed defects below are local, repairable failures of terminology, declared scope, or notation. The distinction between morphisms of E and partial arrows of A should be retained in every repair.

## (C) Minor issues

**S06-01 — The representing morphism and component notation are insufficiently identified.**

- **Anchor:** PDF p.18, Proposition A.3 and opening proof; source 1486–1503; PDF p.19, source 1555–1557.
- **Claim as written:** “Its range idempotents are the partial identities on the regular images of the value maps”; then “a natural transformation $D_f\to Z$,” followed by $f_j(y)$; later “naturality of $p$.”
- **Failure mode:** ambiguous / missing_definition.
- **Why:** “value map” has not been identified as a named part of the representing span. The component notation $f_j$ was introduced at source 1024 for a morphism of E, whereas $f$ here is a partial arrow of A; the intended components belong to the representing morphism $D_f\to Z$. Similarly, $p$ is a partial arrow, so the natural transformation used in the inverse construction is its representing morphism $D_p\to Z$.
- **Evidence:** absence_in_text and structural_argument. The span description at 1036–1045 identifies the morphism but gives no convention transferring its component notation to the partial arrow.
- **Repair:** in the proposition, write “The range of an arrow represented by $Y\xleftarrow{m}D\xrightarrow{v}Z$ is the partial identity on the regular image of $v$.” After 1497, write “Write $f_j:(D_f)_j\to Z_j$ for the components of this natural transformation.” At 1557 use “the naturality of the morphism $D_p\to Z$ representing $p$.” A single earlier explicit component convention could instead cover all later uses.
- **Impact / severity / repairability:** local ambiguity between the two morphism classes; minor; direct textual repair. No change to the stated range or weak-choice properties is required.

**S06-02 — Connectedness is applied to a subfunctor without defining that usage.**

- **Anchor:** PDF p.19, Proposition A.4 proof; source 1567–1573; earlier occurrence on p.14/source 1092–1095.
- **Claim as written:** “take the finite subfunctor ... It is connected”; “A singleton ... is connected as well.”
- **Failure mode:** inconsistent_use / missing_definition.
- **Why:** connectedness was defined at source 261 for restriction idempotents, not for objects or subfunctors. The argument proves that the partial identity on the indicated subfunctor is a connected restriction idempotent.
- **Evidence:** absence_in_text and structural_argument; compare the explicit definition at 261–265 and the partition argument at 1569–1573.
- **Repair:** write “The partial identity on this subfunctor is connected: ...” and “The partial identity on a subfunctor with a singleton in component $i\in\{1,2\}$ and empty other components is connected as well.” Apply the same correction to the earlier Section 8 summary.
- **Impact / severity / repairability:** type of the object possessing the property is obscured; minor, with the intended inference already present; local repair.

**S06-03 — “Central” and “endpoint” are undeclared positional terminology.**

- **Anchor:** PDF pp.19–23, source 1567–1582, 1639, 1655, 1696, 1711, 1790–1811, 1887–1903; first occurrence at source 1092.
- **Claim as written:** “central carrier,” “endpoint carriers,” “central program,” “endpoint programs.”
- **Failure mode:** missing_definition / ambiguous.
- **Why:** the functor components and index set are explicit, but no convention identifies “central” with component 0 or “endpoint” with components 1 and 2. The words are not needed for the categorical construction.
- **Evidence:** absence_in_text; the complete-source search locates uses but no declaration of this convention.
- **Repair:** use “component 0,” “component $i\in\{1,2\}$,” and “the program with index $p_0$ / $p_i$” at the relevant places. For example, 1567–1569 becomes “Let $Y$ be an object of $\mathcal E$. For $y\in Y_0$, take the subfunctor whose components are $\{y\}$, $\{r_1^Yy\}$, and $\{r_2^Yy\}$.”
- **Impact / severity / repairability:** unnecessary local terminology and implicit index interpretation; minor; substitution with existing notation.

**S06-04 — Three local variable declarations are missing.**

- **Anchor:** PDF p.18/source 1527; PDF p.19/source 1567; PDF p.20/source 1598.
- **Claim as written:** “If $gf=hf$”; “For $y\in Y_0$”; “choose a recursive injection $c_j:Y_j\to\N$.”
- **Failure mode:** missing_definition.
- **Why:** $h$ is not introduced in Proposition A.3's proof. Proposition A.4's proof uses $Y$ before introducing its object class. The proof of Lemma A.5 likewise starts with components of an unnamed object $Y$, although its statement quantifies over objects without naming one.
- **Evidence:** absence_in_text in the corresponding local scopes. Earlier uses of these letters in unrelated propositions do not bind them here.
- **Repair:** at 1527 write “For $g,h:Z\rightharpoonup W$ with $gf=hf$, ...”. Start each of the latter two proofs with “Let $Y$ be an object of $\mathcal E$.”
- **Impact / severity / repairability:** locally unbound parameters; minor; direct declarations preserve the quantifiers.

**S06-05 — “Supported arrow” and “support” are not defined.**

- **Anchor:** PDF pp.22–23, Proposition A.8 proof and following paragraph; source 1848, 1854, 1867, 1872–1873.
- **Claim as written:** “a supported arrow”; “it has the required support”; “arrows supported by the corresponding restriction idempotents.”
- **Failure mode:** missing_definition / ambiguous.
- **Why:** the restriction-splitting definition at source 211 states the equation $f=dfe$, but never names it “support.” Support has other mathematical meanings; the local condition is short enough to state directly.
- **Evidence:** absence_in_text; the complete-source search found no definition of supported arrow or support.
- **Repair:** at 1848 use “an arrow $f:Y\rightharpoonup Z$ satisfying $f=dfe$.” At 1854 state $d(m_dgr_e)e=m_dgr_e$. In the Rec comparison say “an arrow satisfying the equations in the definition of the restriction splitting,” or give the corresponding $f=dfe$ condition.
- **Impact / severity / repairability:** undefined shorthand for a central equality condition; minor; replace with the existing definition.

**S06-06 — The superscript on $r_1^V$ is suppressed before the abbreviation is declared.**

- **Anchor:** PDF p.23, Proposition A.9 proof; source 1902; the abbreviation appears later at source 1915.
- **Claim as written:** $\epsilon_1(r_1u,r_1v)$.
- **Failure mode:** missing_definition / inconsistent_use.
- **Why:** Section 8 defined $r_i^V$. The first explicit declaration $r_i=r_i^V$ occurs in Appendix B, after this proof.
- **Evidence:** absence_in_text; compare source 1051–1057, 1902, and 1915.
- **Repair:** write $\epsilon_1(r_1^V u,r_1^V v)$ here.
- **Impact / severity / repairability:** local premature abbreviation; minor; one formula replacement.

**S06-07 — “First truth value” adds an undefined interpretation of a coproduct summand.**

- **Anchor:** PDF p.23, Proposition A.9 proof; source 1902–1904.
- **Claim as written:** “is the first truth value.”
- **Failure mode:** missing_definition.
- **Why:** the definition of decidable equality refers to the first summand of $1+1$. No truth-value interpretation of this object is introduced or required by the proof.
- **Evidence:** absence_in_text; the exact property needed is stated at 1876–1878.
- **Repair:** “Hence $\epsilon_1(r_1^V u,r_1^V v)$ lies in the first summand of $1+1$. Naturality implies that $\epsilon_0(u,v)$ lies in that summand too, contradicting $u\ne v$.”
- **Impact / severity / repairability:** unnecessary terminology; minor; direct reference to the existing definition.

**S06-08 — A frame is the family of isomorphisms, not the individual isomorphisms.**

- **Anchor:** PDF p.20, Appendix A.3 heading/source 1585; PDF p.22, Proposition A.8 proof/source 1827; original naming at source 1064–1065.
- **Claim as written:** “A universal object and its frames”; “The frames of Lemma ...”.
- **Failure mode:** inconsistent_use / misuse_of_prior_work.
- **Why:** Heller (1990), Section 3, printed p.1256, defines a frame at an object as the family of the product, coproduct and free-semigroup isomorphisms together with their inverses. The present text pluralizes the name while discussing one such family.
- **Evidence:** citation; Heller primary-source text, source transcription lines 305–307. The root review also checked this attribution.
- **Repair:** introduce “a frame” as that family, cite Heller Section 3, change the heading to “A universal object and a frame,” and write “The isomorphisms of Lemma ...” when invoking the individual isomorphisms.
- **Impact / severity / repairability:** misuse of established vocabulary rather than invented vocabulary; minor; singular/plural and citation repair.

## (D) Cross-section consistency failures

S06-02 first occurs in Section 8.1 and recurs in Appendix A.2. S06-03 begins in Section 8.1 and propagates through the numerical presentation of the Turing morphism. S06-06 is an abbreviation defined one subsection too late. These should be repaired at their first occurrences as well as at the anchors above.

Definitions confirmed adequate for this portion:

- Restriction idempotents, totality, ranges, the agreement law, restriction splitting, binary restriction products and coproducts, local connectedness, partial monomorphisms, weak choice, prodominical categories and Turing morphisms are defined in Section 2 before use here.
- E, A, the component notation for objects of E, c.e. subfunctors, V and its morphisms are defined in Section 8.
- The three objects H_j are explicitly given at source 1459–1466 before the use at 1553; this is not a missing definition.
- The three isomorphisms are explicit at 1064–1065; their collective name should be singular “frame” as described in S06-08. The term itself is established by Heller and should be retained.
- “Total restriction embedding” is explicitly defined at 1589–1591 before its first named use. Its status as standard literature terminology was not established; it can be avoided by restating the two short equations, but it is not a definition-order defect.
- The word functor, pairing and tuple bijections, encode/decode functions, the partial-equality symbol, and the component domains T_i are defined before their use in their respective arguments.
- “Internal semigroup,” “regular image,” “kernel pair,” and “natural transformation” are standard categorical vocabulary; the latter three are also introduced or defined earlier in the manuscript. The internal-semigroup sentence could state its associative multiplication $M\times M\to M$ for explicit typing, but absence of a textbook definition does not establish a mathematical defect.
- Decidable equality is explicitly defined immediately before Proposition A.9. The use of ordinary set-theoretic domains of definition in this appendix does not substitute “domain” for “restriction idempotent.”

## (E) Acceptance conditions, non-negotiable

1. Identify partial-arrow representatives and their component notation, and refer to the naturality of the representing morphism, at the locations in S06-01. Endpoint: every component formula has a declared source and target. Failure leaves the requested typing review unresolved.
2. Apply connectedness to restriction idempotents, and remove or explicitly translate the positional terms in S06-02–03. Endpoint: the Section 8 summary and Appendix A.2 use the same defined property and component indices. Failure leaves an inconsistent use of a defined term.
3. Add the local declarations in S06-04. Endpoint: Y, g and h are bound in each proof before their components are used. Failure leaves the requested definition-order review unresolved.
4. Replace the support terminology and premature r_1 abbreviation in S06-05–06. Endpoint: the splitting equations and r_1^V are written at their uses. Failure leaves undefined local notation.
5. Replace “first truth value” by the first coproduct summand as in S06-07. Endpoint: Proposition A.9 uses only its stated decidable-equality property. Failure leaves unnecessary undefined terminology.

6. Use the established singular “frame” for the family of three isomorphisms and their inverses, with the Heller citation, as in S06-08. Failure leaves a misuse of established terminology.

These are conditions for accepting the requested exposition correction, not a journal acceptance decision or new mathematical hypothesis.

## (F) Not checked / uncertainty log

Scope: every sentence, formula, heading and proof in baseline source lines 1480–1907 was read, covering blocks B123–B156. Prior definitions at lines 1–295 and 979–1115 were read; the whole source was searched before every absence or late-definition claim. The immediately preceding H_j construction and the definition of Rec were checked separately. PDF locations refer to the immutable 28-page baseline at commit c8feb7e8788d16418dfd1a497913b2b5a46d3670.

The review applies the verified KLR Section 1 principles concerning definitions on first introduction (point 11), consistent notation (14), and unambiguous reading (17), together with the explicit project terminology requirements. It does not prove anew the parameterization theorem, regularity, or the restriction-splitting equivalences, and does not verify novelty. No source changes were made.

Strongest confirmed blocker: no fatal mathematical blocker; the strongest confirmed exposition issue is the undeclared shift from connected restriction idempotents to connected subfunctors (S06-02). Strongest suspected unconfirmed blocker: none established in the requested scope. Most important matter not checked: an independent reconstruction of the Turing-morphism proof. The exposition findings do not depend on unavailable material. Final recommendation: **unknown** for mathematical publication; complete the enumerated local corrections for this terminology/definition-order pass.
