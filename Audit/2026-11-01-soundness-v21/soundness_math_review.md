# Independent mathematical review of the soundness factorization

Scope: the approved plan, lines 600–825, against the v20 model interpretation, the syntactic realization, Appendix A's calculus, and the comparison statement. This report reviews the proposed proof, not the correctness of the whole manuscript. No manuscript files were edited.

## (A) Kill-shots / hard blockers

No hard blocker was found in the following restricted assertion: fix the ambient category \(\mathcal B_{\mathrm{PA}}\), a c.e. arithmetic sentence-axiom presentation \(A\), a set-sized first-order structure \(K\models A\), and an ultrapower \(M=\mathbb N^I/\mathcal U\) by a proper ultrafilter on a nonempty set. The entire interpreted sentence-proof map \(G_Mc_{A,S}\), including its nonstandard proof codes, factors through the transported \(K\)-validity subobject in \(\mathbf{Set}\). The proof does not require preservation of initial algebras.

Two stronger assertions would fail and must not be substituted for that statement:

1. **Arbitrary ambient theories.** The standard numerical functor \(G_{\mathbb N}\) on \(\mathcal B_B\) requires \(\mathbb N\models B\). A semantic model \(K\models A\) does not supply that hypothesis with \(B=A\). If \(B\) proves a \(\Sigma_1\) sentence false in \(\mathbb N\), witness search followed by return of the input is \(B\)-provably the identity but has empty standard graph. Consequently standard evaluation would not descend to the quotient defining \(S_B\). The approved plan correctly uses ambient \(B=\mathrm{PA}\) for arbitrary represented \(A\): plan lines 645–676 and 742–770.
2. **Reflection of categorical source consistency.** Disjointness of interpreted theorem and refutation domains does not imply \(t_A\,\nu^*t_A=0\) in \(\mathcal B_{\mathrm{PA}}\). The interpreting functor need not reflect zero. The source equation encodes a PA-provable absence of opposing proofs, whereas an empty standard interpretation only gives external absence. The actual comparison theorem concludes source *noncoverage*, using preservation of joins; its proof does not reflect zero: `03a-internal-theories.tex`, the proof of `thm:logical-comparison`. That direction is sound.

## (B) Major weaknesses

The v20 manuscript ends the model-interpretation section after the graph interpretation proposition (`06-interpretation-in-models.tex:31–56`). It does not yet prove the factorization. The approved plan can be expanded into a proof as follows.

### 1. Standard-code soundness has a concrete proof

The proof predicate is the finite-tree predicate constructed in `05a-internal-syntax.tex:655–713`; its root-conclusion map is explicitly given there. The sentence restriction is constructed at lines 858–866. In the standard interpretation these are ordinary finite trees. Existential witnesses to c.e. rule membership are witnesses to membership, not further branches or infinitary derivations.

For an assignment \(a\) into \(K\), simultaneous induction on terms and formulas establishes the usual semantic substitution equation on the free-for domain realized in §6. It also establishes dependence only on free variables. These facts validate Appendix A's instantiation, quantifier-distribution, and equality-substitution schemes (`a-syntax-and-theories.tex:525–550`); reflexivity follows from equality, and the first three schemes are Boolean tautologies. Nonlogical axioms are sentences true in \(K\). Modus ponens and generalization preserve validity under every assignment (`a-syntax-and-theories.tex:554–565`). Induction on a standard finite derivation therefore proves that every sentence conclusion is true in \(K\).

Define in \(\mathbf{Set}\)
\[
V_K=\{s\in G_{\mathbb N}S:K\models\varphi_s\},\qquad
v_K:V_K\hookrightarrow G_{\mathbb N}S.
\]
The conclusion function consequently has a unique codomain restriction
\[
e_K:G_{\mathbb N}P_{A,S}\longrightarrow V_K,
\qquad v_Ke_K=G_{\mathbb N}c_{A,S}.
\]
Negation semantics gives \(V_K\cap(G_{\mathbb N}\nu)^{-1}V_K=\varnothing\). Surjectivity onto \(V_K\) is neither claimed nor needed.

### 2. The ultrapower preservation argument is valid

In a set-theoretic metatheory with choice, \(\mathscr U(X)=X^I/{\sim_{\mathcal U}}\) defines a faithful Set endofunctor. Constant families detect unequal maps. The empty set and singleton are preserved. Coordinate pairing preserves products. For equalizers, the equalizer condition holds on a large set; fill its complement with one fixed equalizer element. If the original equalizer is empty, the target equalizer is empty. For finite coproducts, exactly one tag set is large; use the same replacement argument. Surjections split under choice, and hence remain surjective. Preserved surjection–injection factorizations give regular-image preservation. Neither nonprincipality nor countable completeness is needed.

### 3. Comparison must be stated on the actual category

For a predicate presentation \(C\), Łoś's theorem gives a bijection
\[
\eta_C:\mathscr U(C(\mathbb N))\longrightarrow C(M),
\qquad [a_i]\longmapsto[a_i]_{\mathcal U}.
\]
For surjectivity, a representative satisfying \(C\) on a large set can be replaced elsewhere by a fixed member of \(C(\mathbb N)\). If no such member exists, both carriers are empty. For an interpreted functional graph \(\Gamma:C\to D\), Łoś and functionality give
\[
\eta_D\mathscr U(G_{\mathbb N}\Gamma)=G_M\Gamma\,\eta_C.
\]
The predicate category is equivalent to \(\mathcal B_B\), rather than literally equal to it. Transport these maps through the specified equivalence (or explicitly through its coding bijections) to obtain the claimed natural isomorphism on \(\mathcal B_B\). This is a presentation issue, not a mathematical obstruction.

### 4. The transported factorization has the required types

With \(\eta:\mathscr U G_{\mathbb N}\cong G_M\), define
\[
e_{K,\mathcal U}=\mathscr U(e_K)\eta_{P_{A,S}}^{-1}:
G_MP_{A,S}\longrightarrow\mathscr U(V_K),
\]
\[
v_{K,\mathcal U}=\eta_S\mathscr U(v_K):
\mathscr U(V_K)\hookrightarrow G_MS.
\]
Then
\[
v_{K,\mathcal U}e_{K,\mathcal U}
=\eta_S\mathscr U(v_Ke_K)\eta_{P_{A,S}}^{-1}
=G_Mc_{A,S}.
\]
The second map is monic. Preservation of pullbacks and the empty set, together with naturality for \(\nu\), gives disjointness of its image and its inverse image under \(G_M\nu\). Regular-image preservation identifies the interpreted theorem subobject with the conclusion image, so it too is disjoint from its negated inverse image.

This argument covers **all** of \(G_MP_{A,S}\). A code in its carrier is represented, on a large set, by standard valid finite proof codes; filling the remaining coordinates puts it in the image of \(\eta_{P_{A,S}}\). No external induction on a nonstandard proof tree occurs.

## (C) Minor issues

- Keep \(P_A\) (all formula conclusions) separate from \(P_{A,S}\) (sentence conclusions). The factorization uses the latter.
- Keep numerical standard interpretation \(G_{\mathbb N}\) separate from semantic truth in \(K\). No hypothesis \(\mathbb N\models A\) is used.
- \(V_K\) and its transported image are Set-subobjects. Neither is asserted arithmetically definable or an internal subobject of \(\mathcal B_{\mathrm{PA}}\).
- A useful explicit semantic characterization is
  \[
  [s_i]\in\operatorname{im}(v_{K,\mathcal U})
  \iff\{i:K\models\varphi_{s_i}\}\in\mathcal U.
  \]
  Here representatives are sentence-valued, and changing representatives does not change the condition. On diagonal standard sentence codes this agrees with ordinary \(K\)-truth. This suffices to explain the transported validity object without identifying it with an ordinary satisfaction predicate for nonstandard formulas.
- The failure to preserve initiality has no adverse role in the proof. For a nonprincipal ultrafilter on \(\mathbb N\), the class \([i]\) shows that the transported \(1+X\)-algebra has elements not generated by zero and successor; this proves failure of initiality, not failure of the factorization.

## (D) Cross-section consistency failures

No inconsistency was found between the proposed restricted factorization and the inspected definitions. Its compatibility requirements are substantive:

1. Cite §6's actual finite-tree realization when identifying standard carrier elements with ordinary derivations.
2. Establish finite limits, finite coproducts, and regular images for \(G_M\) using the predicate presentation; v20 states range preservation for \(F_M\) but does not yet state the full total-category preservation result.
3. Apply the image/range proposition to the Set validity subobject. It yields consistency of the *interpreted* sentence theory. Apply the comparison theorem separately to obtain source noncoverage.
4. Do not replace the selected ultrapower of \(\mathbb N\) by an arbitrary model of PA. The standard-code comparison used in this proof is absent for such a replacement.

## (E) Acceptance conditions, non-negotiable

The proposed new result is acceptable as a proof once the manuscript contains:

1. Fixed ambient \(\mathcal B_{\mathrm{PA}}\), separate \(K\models A\), and the exact sentence-proof carrier.
2. Finite-derivation soundness with open-formula validity, substitution, quantifier side conditions, equality, and both inference rules accounted for.
3. The natural comparison with explicit handling of empty predicates and exceptional coordinates, transported through the predicate equivalence.
4. The two typed maps above, their composite equation, and the pullback proof of negation-disjointness.
5. A statement that the conclusion covers the entire interpreted proof object; no assertion of initial-algebra preservation, source zero reflection, or internal definability of the semantic validity subobject.

## (F) Not checked / uncertainty log

- This review did not reprove the general categorical comparison theorem, the recursion-category axioms, or every construction in Appendix A.
- It inspected the derivation realization and its source typing, but did not independently reconstruct every index compiler or every numerical substitution recursion in §6.
- It did not independently verify the final bibliography's edition/page numbering for the soundness and ultrapower sources. The ultrapower and factorization arguments above have been checked directly.
- The construction agent's insertion draft `tmp/soundness21/soundness_draft.tex`, lines 1–388, was subsequently read in full. Its mathematical proof and displayed types pass this review. The exact final integrated source, bibliography numbering, and compiled output remain the root agent's verification task.

### Review of the concrete insertion draft

The draft supplies the previously missing arguments: total-functor regularity at lines 19–41; the semantic substitution lemma at lines 78–139; all seven logical schemes and both rules at lines 141–203; ultrapower preservation at lines 220–255; the comparison on predicate objects and its transport through the equivalence at lines 261–307; and the factorization, target disjointness, and image identification at lines 309–366. Lines 382–388 explicitly cover the full proof carrier. No defect was found in these arguments.

One minor typing edit was requested at lines 45–46: replace “the variable object with carrier \(\mathbb N\) in \(\mathcal B_{\mathrm{PA}}\)” by the explicitly typed object \(V=J_{\mathrm{PA}}(x=x)=(\omega,1_\omega)\) in \(\mathcal B_{\mathrm{PA}}\), whose standard interpreted carrier is \(\mathbb N\). This avoids conflating a categorical object with its Set interpretation. The construction agent confirms this correction has been made.

A focused subsequent check of `tmp/soundness21/arithmetic_draft.tex`, lines 1–256, found no mathematical blocker. The explicit assumption that every PA axiom is derivable from the external c.e. sentence set suffices to translate each finite PA proof. The resulting universal reduction implications are claimed true in \(\mathbb N\), rather than PA-provable, and therefore transfer to the chosen ultrapowers. The partial search only requires PA proofs of output correctness and exact domain; target disjointness gives functionality and hence the full target graph. The comparison concludes source noncoverage without reflecting zero. The recursive separator is lifted as a partial source morphism, so source-provable totality is unnecessary.

Strongest confirmed blocker: none for the restricted theorem or the concrete draft. Strongest suspected blocker: an unintended inference of source categorical consistency from target disjointness would be invalid, but neither the draft nor the approved comparison theorem makes that inference. Most important unchecked point: the final integrated manuscript's cross-references and compilation. Recommendation: accept the restricted soundness-factorization proof with the minor object/carrier wording correction; no recommendation on the whole paper from this bounded review.
