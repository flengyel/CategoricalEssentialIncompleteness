# Independent mathematical review: uniform family of arithmetic theories

Scope: the complete insertion draft `tmp/uniform22/uniform_draft.tex` (209 lines before two local typing clarifications), read against the v21 syntactic realization, Appendix A, the standard-code soundness proposition, and the arithmetic comparison. This is an author-side mathematical check of the new subsection, not a whole-paper or novelty assessment. No manuscript files were edited by this reviewer.

## (A) Kill-shots / hard blockers

No confirmed blocker was found in Proposition `prop:arithmetic-theory-fibers` or Theorem `thm:uniform-independent-sentences`. Their scope is a family in the fixed category \(\mathcal B_{\mathrm{PA}}\), with independence asserted for externally consistent standard fibers.

The required special base change is proved. It is not inferred from a general assertion that pullback preserves initial algebras.

## (B) Major weaknesses

No major weakness remains in the inspected proof. The central claims were checked as follows.

| Draft anchor | Typed claim and check | Status |
|---|---|---|
| Opening definitions, lines 4–27 | \(E=I(\omega)\in\mathcal B\); \(G_{\mathbb N}E=\mathbb N\). The \(\Sigma_1\) predicate \(\operatorname{Sent}(z)\land(\operatorname{Ax}_{\mathrm{PA}}(z)\lor\exists y\,G(e,z,y))\) presents \(A\hookrightarrow E\times S\). Individual axiom subobjects use its literal numeral specialization. | Correct. No identification of extensionally equal presentations is claimed. |
| Family rule definitions, lines 29–55 | \(R_0^E=(E\times L)+A\), \(R_n^E=E\times R_n\) for \(n=1,2\), and the displayed conclusion maps land in \(F_E=E\times\mathrm{Fm}\). The maps \(d_n\) duplicate the parameter in all premises. Lemma 5.8 applies with this \(F_E\). | Correct, including the nullary premise map to the terminal object. |
| Image construction, lines 57–64 | The sentence pullback \(c:P\to E\times S\) has regular image \(\mathcal T\hookrightarrow E\times S\). Appendix A's least-image theorem applies to the full conclusion map. The partial-inverse hypothesis for the image mono is supplied by the earlier regularity lemma for \(\mathcal B\). | Correct. No initiality of the sentence-restricted object is asserted. |
| Fiber proposition, complement and slice equivalence | PA proves the disjoint exhaustive alternatives \(x=\bar e\) and \(x\ne\bar e\). Thus \(E\cong1+E_{\ne e}\). Finite extensivity gives \(\mathcal B/(E\times\mathrm{Fm})\simeq\mathcal B/\mathrm{Fm}\times\mathcal B/(E_{\ne e}\times\mathrm{Fm})\). | Correct special decomposition for each numeral. |
| Fiber proposition, decomposition of \(H_E\) | For arity zero, the components are the inverse images of \(R_0^E\) under its conclusion map. For positive arity, every premise has the conclusion's parameter, so a pullback cannot mix the two components. The premise pullbacks become precisely the two component rule pullbacks; their arrow maps agree by pullback uniqueness. | Correct. This is the substantive additional argument. |
| Fiber proposition, component initiality | The algebra category decomposes as the product of the component algebra categories. If \((P_e,P_{\ne e})\) is initial, testing against \((Q,P_{\ne e})\) gives existence of a morphism \(P_e\to Q\). Pairing two candidates with \(1_{P_{\ne e}}\) gives uniqueness. | Correct without separately assuming initiality in the complementary component. |
| Fiber proposition, final paragraph | The component's initiality identifies it with the existing derivation algebra for \(A_{\Gamma_e}\). Sentence pullbacks then give the displayed square. Only at this point is stability of regular images used to identify the generated-theory fiber. | Correct order of dependencies. |
| Uniform theorem, search construction | One \(\Sigma_1\) relation on paired input \(\langle e,x\rangle\) gives a partial source arrow \(\ell:\omega\times\omega\rightharpoonup\omega+\omega\). PA proves output soundness and exact domain \(C\lor C'\); functionality of the desired output relation is required only in the interpreted consistent fiber. | Correct. No source consistency or totality of \(\ell\) is assumed. |
| Uniform theorem, Turing equation | The parameterized Turing property gives total \(g:\omega\to\omega\) with \(\tau(g\times1)=b^{-1}\ell\). Precomposition with \(\langle1,g\rangle\) gives \(hg=\ell\langle1,g\rangle\). Hence \(q=\theta I(g):E\to S\) is total in \(\mathcal B\). | All composites and domains check. |
| Uniform theorem, independence | For consistent standard \(\Gamma_e\), soundness makes \(C(e,-)\) and \(C'(e,-)\) disjoint. If the first holds at \(n=F_{\mathbb N}(g)(e)\), the search returns the odd tag, so \(n\in D_1\), and the existing reduction gives the second. The converse case uses the even tag and \(D_0\). Both contradict disjointness. | Correct for the stated standard-fiber scope. |

The categorical fiber proof replaces the proposed insertion/deletion proof completely. It reuses Appendix A's endofunctor and least-image theorem, and the main section's realization theorem. It does not repeat their constructor, substitution, fold, or regular-image proofs.

## (C) Minor issues

Two local typing clarifications were sent to the constructor and root:

1. **Anchor:** opening axiom-subobject paragraph and fiber proof's “the predicate object \(x\ne\bar e\).” **Claim as written:** a subobject of objects in \(\mathcal B\) is described as being in the predicate presentation. **Failure mode:** `ambiguous`, minor. **Evidence:** `structural_argument`; the predicate category is equivalent to \(\mathcal B\), not literally the same category. **Repair:** say the axiom predicate defines a subobject in \(\mathcal B\) via the predicate presentation, and explicitly put \(E_{\ne e}=(\omega,[x\ne\bar e]_{\mathrm{PA}})\in\mathcal B\). **Impact:** fixes object/presentation wording; no proof reconstruction.
2. **Anchor:** fiber proof, “Under this slice equivalence, it is naturally isomorphic to \(H_{A_{\Gamma_e}}\times H_{\ne e}\).” **Failure mode:** `ambiguous`, minor. **Evidence:** `structural_argument`; these endofunctors have different domain categories before transport. **Repair:** name the equivalence \(\Xi_e\) and write \(\Xi_eH_E\cong(H_{A_{\Gamma_e}}\times H_{\ne e})\Xi_e\). **Impact:** states the typed comparison already proved by the following pullback argument.

These are local clarifications of an otherwise valid argument. Their completion is the integration step; no further mathematical review round is needed for them.

## (D) Cross-section consistency failures

None found in the inspected material.

- The external set \(\Gamma_e\) is distinct from the internal axiom subobject \(A_{\Gamma_e}\).
- The full derivation object lies over \(E\times\mathrm{Fm}\); the sentence restriction lies over \(E\times S\).
- The family \(\mathcal T\) is a regular image in \(\mathcal B\); its partial identity lies in \(\operatorname{Split}(S_{\mathrm{PA}})\).
- The source arrows \(\ell,g\) lie in \(S_{\mathrm{PA}}\); \(q=\theta I(g)\) explicitly uses the inclusion into the splitting.
- The total map \(q\) is defined on every presentation index. Its independence assertion is conditional on external consistency of the standard fiber. No internal subobject of consistent indices is introduced, and no zero-reflection inference is made.
- Existing Appendix A arguments are invoked by reference. The special complemented-fiber argument and the extra presentation parameter in the Turing argument are the new proofs.

## (E) Acceptance conditions, non-negotiable

The inspected draft supplies the mathematical endpoints below; integration must retain them.

1. Literal specialization of the universal \(\Sigma_1\) axiom predicate for each \(A_{\Gamma_e}\). Without this, the categorical fiber identification would be unsupported by mere external extensional equality.
2. Premise and conclusion maps retaining the same parameter, including explicit nullary rule data. Without this, the endofunctor decomposition could fail.
3. The complemented-numeral decomposition, typed natural comparison, and component-initiality proof. Without them, the required base-change claim would remain unproved.
4. Sentence-pullback identification before applying stability of regular images. Without it, the conclusion about generated-theory fibers would not follow.
5. One partial search relation, total Turing parameter \(g\), and the equation \(hg=\ell\langle1,g\rangle\). Without them, uniformity would not be established.
6. The externally consistent standard-fiber scope and explicit \(q=\theta I(g)\). Stronger internal-consistency or arbitrary-model assertions must not be substituted.

## (F) Not checked / uncertainty log

This review did not independently reprove every numerical compiler, all of Appendix A, the retained applications, or every literature attribution. It makes no novelty claim. The final integrated numbering and PDF compilation are the root agent's checks.

Strongest confirmed blocker: none. Strongest suspected unconfirmed blocker: none in the inspected statements. Most important unchecked item: the exact final integrated source and rendering. The mathematical assessment does not depend on unavailable material. Whole-paper acceptance recommendation: unknown, because the review is deliberately limited to this addition; the two inspected mathematical claims have no remaining substantive defect.
