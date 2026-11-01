# Hostile review of the new soundness and arithmetic sections

Manuscript: *Logical consequence and essential incompleteness in recursion categories*, version 22. This author-side audit concerns §6, especially §§6.3–6.4, and §§7.1–7.2 (printed/PDF pp. 25–33). Source files are `sections/06-interpretation-in-models.tex` (abbreviated **06**), `sections/08-essential-incompleteness-of-arithmetic.tex` (**08**), and `sections/08a-uniform-theories.tex` (**08a**). Line numbers below refer to the unmodified v22 sources. The relevant categorical definitions, realization lemmas in §5, comparison theorem, and Appendix A were consulted. No manuscript file was edited by this reviewer.

## (A) Kill-shots / hard blockers

No confirmed fatal mathematical defect was found in the new results. In particular, the two delicate arguments have the required structure:

- Proposition 7.5 proves base change along a complemented numeral inclusion by decomposing the slice and its inference endofunctor. It does not assume that an arbitrary pullback preserves initial algebras.
- Theorem 7.6 obtains one parameterized search morphism and one total Turing parameter map. The equation \(hg=\ell\langle1,g\rangle\) is correctly typed and gives independence in each externally consistent standard fiber.

This conclusion is restricted to the inspected material and dependencies described below; it is not a certification of the whole manuscript.

## (B) Major weaknesses

No major mathematical weakness is confirmed. The central claims were checked as follows. A claim described as checked has a derivation from the manuscript's stated hypotheses; it is not being accepted on the basis of the preceding review.

| Anchor | Data, hypotheses, and check | Status |
|---|---|---|
| 06:204–265, p. 25, Lemma 6.5 | \(\sigma:\mathbb N\to|K|\); admissible finite substitution; values of free variables determine term values and truth. The quantified case separates \(y=x\), absence of free \(x\), and the free-for case. In the last case \(y\notin\mathrm{FV}(t)\) justifies commuting the assignment changes. | Derivation checks. The proof concerns semantic substitution and does not duplicate Appendix A's categorical construction. |
| 06:267–332, p. 26, Proposition 6.6 | \(\Gamma\) is c.e.; \(K\models\Gamma\); \(G_{\mathbb N}\) interprets the codes. Each of the seven logical schemes is valid, MP and generalization preserve validity, and induction covers all standard finite trees. Corestriction gives \(e_K\); monicity gives uniqueness. Negation is realized by the actual negation-code operation. | Derivation checks. No assumption \(\mathbb N\models\Gamma\) is used. |
| 06:349–384, pp. 26–27, Lemma 6.7 | Nonempty index set, proper ultrafilter, and ambient choice are stated. Coordinate replacement handles equalizers and coproduct summands, including empty carriers. Surjections split in the metatheory and hence remain surjective under the functor. | Derivation checks. The hypotheses are used. |
| 06:390–435, p. 27, Lemma 6.8 | \(\eta:\mathscr U G_{\mathbb N}\Rightarrow G_M\) has domain \(\mathcal B_{\mathrm{PA}}\) and codomain Set. The predicate component sends a class of elements of \(C(\mathbb N)\) to its class in \(M\). Łoś gives membership; replacement gives surjectivity; functional graphs give naturality. Fullness of \(J_{\mathrm{PA}}\) transports the comparison to the actual category. | Derivation checks, conditional on the cited Łoś theorem. Changing a chosen presentation does not change the component, by the same naturality square. |
| 06:437–495, pp. 27–28, Theorem 6.9 | \(v_{K,\mathcal U}:\mathscr U(V_K)\hookrightarrow G_MS\) and \(e_{K,\mathcal U}:G_MP_{A,S}\to\mathscr U(V_K)\) compose with the stated types. Naturality transfers the factorization; finite-limit preservation transfers empty intersection; regular-image preservation identifies the theorem subobject. | Derivation checks. The result needs neither preservation of initial algebras nor definability of the validity subobject in arithmetic. |
| 08:81–134, p. 29, Lemma 7.1 | \(\theta\) is PA-provably total by the realized substitution. For each standard diagonal computation, a finite PA-proof exists. Derivability of every PA axiom from \(\Gamma\) transfers each finite proof. The universal implications are established in \(\mathbb N\), then transferred to \(M\equiv\mathbb N\). | Derivation checks. The text does not claim these universal implications are PA-provable for an arbitrary external \(\Gamma\). |
| 08:136–179, pp. 29–30, Lemma 7.2 | The search has a PA-proved exact domain \(C\lor C'\), but is only a partial source morphism. In a model where the predicates are disjoint, \(R\) is functional; existence plus output soundness gives the full graph. | Derivation checks. No unjustified totality or source consistency is used. |
| 08:181–260, pp. 30–31, Theorem 7.3 and Corollary 7.4 | Completeness supplies \(K\models\Gamma\); §§6.3–6.4 supply disjoint target theorem/refutation domains; Lemmas 7.1–7.2 supply the two reductions and lift. The comparison theorem gives noncoverage. For a recursive separator the source lift need only be partial. | Derivation checks. The comparison does not reflect target zero to source zero. |
| 08a:4–66, p. 31, family construction | \(E\in\mathcal B_{\mathrm{PA}}\); \(i:A\hookrightarrow E\times S\); \(R_0^E=(E\times L)+A\), \(R_n^E=E\times R_n\). Every premise and conclusion has the same parameter. Lemma 5.8 applies to \(F_E=E\times\mathrm{Fm}\); Appendix A identifies its regular image. | Construction checks. The formula axioms and family derivation carrier are not silently identified with their external sets. |
| 08a:73–149, p. 32, Proposition 7.5 | The numeral complement gives \(E\cong1+E_{\ne e}\). Extensivity gives the slice equivalence; common parameters prevent a rule from mixing components. The induced equivalence of algebra categories preserves initial objects. Testing the initial pair against \((Q,P_{\ne e})\) proves initiality of its first component. Sentence restriction and stable regular images give the displayed theory fiber. | Derivation checks. The paragraph comparing pullbacks needs the local precision noted in C3, but its mathematical inference is valid. |
| 08a:151–214, pp. 32–33, Theorem 7.6 | The conclusion index represents \(c:P\to E\times S\), so its range is the stated uniform \(\Sigma_1\) predicate. Turing parameterization gives \(\tau(g\times1)=b^{-1}\ell\); precomposition yields \(hg=\ell\langle1,g\rangle\). Thus \(q=\theta I(g):E\to S\). At a consistent standard index, positive proof forces the opposite diagonal set and hence negative proof, and conversely. | Derivation checks. \(q\) is total on all presentations; independence is asserted only at consistent standard indices. |

## (C) Minor issues

### C1. State which coordinate representatives are sentence codes

**Anchor:** 06:497–509, p. 28: “For a sentence-code representative \(s=[s_i]\in G_MS\).”

**Failure mode:** `ambiguous`. **Severity:** minor. **Evidence:** `structural_argument`. Membership of \([s_i]\) in the interpreted sentence predicate requires the coordinates to be sentence codes only on a set in the ultrafilter. The subsequent expression \(\varphi_{s_i}\) requires each relevant coordinate to be a sentence code. The comparison lemma guarantees a representative with every coordinate in \(G_{\mathbb N}S\), but the phrase does not explicitly make that choice. This is a local omission, not a false theorem.

**Repair:** “Choose \((s_i)\in(G_{\mathbb N}S)^I\) representing \(s\in G_MS\) under \(\eta_S\). Then …”. The membership equivalence becomes literally defined at every coordinate. **Downstream impact:** fixes the pointwise satisfaction description; no theorem changes.

### C2. Declare the two endofunctor types at their introduction

**Anchor:** 08a:107–113, p. 32, Proposition 7.5 proof: “Let \(H_E\) be the inference endofunctor for the family rules, and let \(H_{\ne e}\) be formed by restricting those rules.”

**Failure mode:** `missing_definition` (local typing omission). **Severity:** minor. **Evidence:** `absence_in_text` at introduction, repaired implicitly by the ensuing displayed composite and Appendix A. The displayed natural comparison is well typed, but its component endofunctors' categories must be reconstructed by the reader.

**Repair:** Explicitly write \(H_E:\mathcal B/(E\times\mathrm{Fm})\to\mathcal B/(E\times\mathrm{Fm})\) and \(H_{\ne e}:\mathcal B/(E_{\ne e}\times\mathrm{Fm})\to\mathcal B/(E_{\ne e}\times\mathrm{Fm})\), referring to Appendix A's construction. **Downstream impact:** makes the algebra-category equivalence immediately readable. It does not require repeating the definition or functoriality proof from Appendix A.

### C3. Replace equality language by the canonical pullback isomorphism

**Anchor:** 08a:114–128, p. 32: “The parameter-\(e\) component is therefore exactly the pullback which defines \(B_n\) for \(A_{\Gamma_e}\).”

**Failure mode:** `inconsistent_use` of equality/isomorphism language. **Severity:** minor. **Evidence:** `structural_argument`. The argument decomposes objects under an equivalence and compares independently chosen pullbacks. It establishes a canonical isomorphism, not literal equality of their chosen carriers. The earlier natural-isomorphism display is the correct claim.

**Repair:** “The first component is canonically isomorphic to the pullback defining \(B_n\) for \(A_{\Gamma_e}\); the second is canonically isomorphic to the corresponding pullback for \(H_{\ne e}\).” Preserve the following sentence explaining naturality by pullback uniqueness. **Downstream impact:** avoids a needless strictness claim; the proof remains unchanged mathematically.

### C4. Describe specialization as the actual predicate definition

**Anchor:** 08a:19–21, p. 31: “Their internal axiom subobjects … use the literal specializations …”.

**Failure mode:** `ambiguous` wording. **Severity:** minor. **Evidence:** `absence_in_text` of a precise meaning for “use,” although the intended representation is established later. “Literal specializations” is not a new mathematical object and is unnecessary terminology.

**Repair:** “For each \(e\in\mathbb N\), the axiom subobject \(A_{\Gamma_e}\hookrightarrow S\) is represented by the predicate \(\operatorname{Ax}(\bar e,z)\).” **Downstream impact:** retains the essential dependence on the chosen presentation, without the adjective. Do not weaken this to arbitrary predicates with the same standard extension.

### C5. Use ordinary descriptions of the two algebra components

**Anchor:** 08a:119–139, p. 32: “child conclusions,” “parameter-\(e\) component,” “initial family algebra.”

**Failure mode:** `ambiguous` expository shorthand. **Severity:** minor. **Evidence:** `structural_argument`. The argument is in a slice category and applies to arbitrary slice objects \(Q\), not only to the tree realization. “Child conclusions” momentarily substitutes tree terminology for the morphisms being compared. “Initial family algebra” is understandable but not needed as another name.

**Repair:** In the pullback argument say that “the \(n\) premise coordinates and the conclusion have the same parameter,” and use “first component,” “second component,” and “initial \(H_E\)-algebra.” **Downstream impact:** makes the categorical argument independent of its numerical model, while preserving its mathematical content.

### C6. Remove the concluding repetition of total-domain scope

**Anchor:** 06:511–517, p. 28: “Thus the factorization holds on the entire interpreted proof object, including its nonstandard proof codes.”

**Failure mode:** `inconsistent_use` is not alleged; this is expository redundancy only. **Severity:** minor. **Evidence:** `structural_argument`. Theorem 6.9 already has the whole object \(G_MP_{A,S}\) as the domain of its total function, and the previous sentence describes representatives of every element. The final sentence repeats that scope rather than making an additional inference.

**Repair:** Retain the useful explanation that elements are represented by families of standard derivations, and delete the final “Thus” sentence. If an explicit mention of nonstandard elements is useful, attach it to the representative description once. **Downstream impact:** none; the theorem's full quantified scope must remain.

### C7. Remove the informal term “sentence-conclusion pullback” when it functions as a name

**Anchor:** 08:27–28, p. 29: “Thus \(P_\Gamma\) is the sentence-conclusion pullback of the full derivation object.”

**Failure mode:** `ambiguous` expository compression. **Severity:** minor. **Evidence:** `structural_argument`. A pullback is taken along a morphism, and the compressed compound name suppresses that morphism. The definition in §6 is adequate, so the issue is unnecessary terminology rather than a missing construction.

**Repair:** “Thus \(P_\Gamma\) is obtained by pulling back the full conclusion morphism along \(S\hookrightarrow\mathrm{Fm}\).” **Downstream impact:** none. Cite the existing definition; do not repeat its proof.

No new mathematical noun such as “finite coproduct table” occurs in the audited material. Terms such as “regular image,” “restriction idempotent,” “slice category,” “initial algebra,” “natural isomorphism,” “numeral,” and “ultrapower” have their ordinary mathematical meanings here. “Theory subobject” is a locally defined object of the paper, not an unsupported replacement for standard categorical structure.

## (D) Cross-section consistency failures

No substantive cross-section inconsistency was found in the inspected dependencies.

- \(S_{\mathrm{PA}}\), its restriction splitting, and its total subcategory are distinguished. The use of \(I(g)\) in \(q=\theta I(g)\) is necessary and correctly supplied.
- The predicate category is used through \(J_{\mathrm{PA}}\); it is not declared literally equal to \(\mathcal B_{\mathrm{PA}}\).
- \(\Gamma_e\) is an external presentation, while \(A_{\Gamma_e}\), the derivation object, and its image are categorical objects/subobjects.
- The validity subobjects are in Set. No definable arithmetic satisfaction predicate or internal subobject of consistent presentation indices is claimed.
- The full derivation algebra lies over formulas; the sentence object is a pullback of its conclusion map. The sentence restriction is not incorrectly called an initial algebra for the unmodified inference endofunctor.
- Theorem 7.3 and Theorem 7.6 use external consistency only where it is stated. Neither reflects interpreted zero to source zero.
- The new family proof refers to Appendix A for the inference construction and its least-image property. It does not repeat the constructor, substitution, induction, or regular-image proofs there.

The minor equality-language drift in C3 is the only categorical consistency repair identified.

## (E) Acceptance conditions, non-negotiable

1. **Well-defined coordinate satisfaction, §6.4:** specify representatives in \((G_{\mathbb N}S)^I\) before using \(\varphi_{s_i}\). Verifiable endpoint: every coordinate satisfaction expression is defined. Failure prevents accepting that pointwise description as written, but does not invalidate Theorem 6.9.
2. **Typed endofunctor comparison, Proposition 7.5:** display both endofunctor categories and retain the natural comparison \(\Xi_eH_E\cong(H_{A_{\Gamma_e}}\times H_{\ne e})\Xi_e\). Use canonical-isomorphism language for the component pullbacks. Verifiable endpoint: every functor composite and comparison has a declared type. Failure leaves a local exposition defect; it is not evidence of a false fiber theorem.
3. **Preserve the presentation specialization, Proposition 7.5:** replace “literal specializations” with the precise representative-predicate assertion, retaining \(\operatorname{Ax}(\bar e,z)\). Verifiable endpoint: the first component has the actual axiom predicate used for \(\Gamma_e\). Replacing this by equality of standard extensions alone would leave the categorical fiber assertion unsupported.
4. **Preserve the scoped independence assertion, Theorem 7.6:** the total morphism may range over every presentation index, but independence must remain conditional on external consistency of the standard fiber. Verifiable endpoint: no stronger internal-consistency or arbitrary-model statement is introduced. Such a strengthening would require a new proof.

The remaining minor prose repairs can be implemented without changing theorem statements or Appendix A. No claim needs to be dropped on the present evidence.

## (F) Not checked / uncertainty log

This review read the three target source files, the relevant definitions and proof dependencies in §§2–5, and the inference/image construction in Appendix A. It checked the substantive new arguments independently. It used extracted v22 PDF text to verify page anchors; it did not inspect page images or compile revised files.

The full numerical compiler construction in §5 was consulted as a dependency, not rederived in every primitive-recursive coding detail. No whole-paper novelty assessment was attempted. The cited literature was not independently reopened; in particular the application of Łoś's theorem was checked mathematically, while its bibliographic theorem number was not reverified. No result about an arbitrary arithmetic model outside the stated ultrapower scope was tested or inferred.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none in the inspected new claims. Most important item not checked: the low-level arithmetization underlying every index and the exact revised rendered manuscript. The mathematical conclusion does not depend on unavailable manuscript material. Final recommendation: **unknown** as a whole-paper publication judgment; the inspected additions have no confirmed fatal or major defect and admit the concrete local repairs above.
