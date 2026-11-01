# (A) Kill-shots / hard blockers

None established in this review.

**Local disposition: PASS for §7.2, “An indexed family of arithmetic theories,” in version 24 of _Logical consequence and essential incompleteness in recursion categories_.** This is a new author-side audit of the current text, not reliance on the earlier review's disposition. The reviewed source is `tmp/review25/round1/08a-uniform-theories.tex`, SHA256 `bcf6666d968ac4a68e6351bf2c1497ee1d86724d8c33dfef26fecaf266f267bd`. Printed and PDF pages 31–35 contain the section. Source line numbers below refer to that frozen file.

The audit covers correctness, explicit typing, and the use of the cited internal dependencies. It makes no claim of formal verification, whole-paper acceptance, or novelty certification.

# (B) Major weaknesses

None confirmed. The following potentially substantial failure points were tested and did not yield a defect.

1. **Existence of the family algebra.** At p. 32, lines 65–109, “Lemma 5.8 gives its initial algebra,” the displayed data have the required types in `B`: `F_E=E×Fm`, `R_0^E=(E×L)+A`, `R_n^E=E×R_n`, `p_n^E:R_n^E→F_E^n`, and `q_n^E:R_n^E→F_E`, for `n=0,1,2`. The nullary premise is explicitly the terminal morphism. Lemma 5.8 quantifies over an arbitrary object `F` and arbitrary finite rule data of precisely these types; it does not restrict `F` to the unparameterized formula object. Its tree-and-fold proof applies here with `T=PA` and `N=2`. The family adds no unproved preservation of an initial algebra. **Evidence: structural argument and inspected dependency. Status: established within the manuscript's hypotheses.**

2. **Fibers and initiality.** At pp. 33–34, Proposition 7.5, lines 151–301, the complement is the decidable numeral complement `E_{≠e}` in `B`, and finite extensivity applies to the isomorphism `[epsilon_e,u_e]:1+E_{≠e}→E`. The functor `Xi_e` is a covariant equivalence from `B/F_E` to the product of the two indicated slices; its object and morphism actions are stated. Because each premise has the conclusion's parameter, each rule pullback decomposes into the two parts. This is the specific reason for `zeta`, rather than an unsupported general assertion that base change preserves initial algebras. The component and naturality equations are composable. Conjugation by `zeta^{-1}` gives the correctly directed algebra structure, and full faithfulness and essential surjectivity transfer along `Xi_e`. Testing the image of the initial algebra against `(Q,P_{≠e})` proves initiality of its first component. Pairing competing first-component arrows with `1_{P_{≠e}}` proves uniqueness. **Evidence: derivation. Status: established.**

3. **Numerical meaning of the family predicate.** At p. 32, lines 35–63, and pp. 34–35, lines 304–333, `v:J(D)→E×S` is built from the numerical projections. It is not an unspecified presentation isomorphism that might permute parameters or conclusions. The composite `v^{-1}cu:J(P_0)→J(D)` is a morphism of `B`, and fullness gives a morphism `gamma_c:P_0→D` in the predicate category. Lemma 5.2 and its support and totality conditions supply the exact-domain graph. Consequently `exists d G_{a_c}(d,<e,z>)` represents the image under those fixed coordinates. Proposition 7.5 identifies the corresponding fiber subobjects over `S`; in the predicate category this is PA-provable equivalence of their carrier predicates. Both predicates PA-provably imply `Sent`, so the stated equivalence is universally quantified over all numerical `z`, not only sentence codes. **Evidence: derivation using Lemma 5.3's subobject description. Status: established.**

4. **Uniformity and the diagonal contradiction.** At p. 35, Theorem 7.6, lines 344–413, `R(e,x,z)` is a single Sigma_1 formula in the fixed PA language. Lemma 5.2 yields one index `a_ell`, hence one partial morphism `ell:omega×omega⇀omega+omega` in `S_PA`. No consistency assumption is needed for that search: when both predicates hold it can choose one permitted output. The parameterized Turing property gives a total `g:omega→omega`; precomposition yields `hg=ell<1,g>` with the displayed source and target. `q=theta I(g)` is therefore a total morphism `E→S` in `B`. For a standard consistent presentation, a model `K` gives disjoint standard proof and refutation predicates. At `n=F_N(g)(e)`, either predicate makes `h(n)` have the opposite parity, and Lemma 7.1 supplies the other predicate, contradicting disjointness. Every axiom of PA is available because of the definition of `Gamma_e`. The argument neither assumes `N models Gamma_e` nor reflects target emptiness to a source zero. **Evidence: derivation. Status: established.**

# (C) Minor issues

No necessary correction identified in the scoped text. No empty phrase, invented terminology, omitted type, or compressed inference was found that prevents reconstructing the argument from the displayed data and its expressly cited definitions.

Finite powers are the finite products declared in Appendix A, including the nullary object and morphism conventions. “Inference endofunctor,” “sentence theory,” “restriction splitting,” and “range” have manuscript definitions. They are not being used as unexplained replacements for mathematical data. Elementary consequences of the stated pullback and coproduct constructions do not need another copy of the appendix's proof.

# (D) Cross-section consistency failures

None confirmed. The explicit-type checks below record the relevant interfaces.

**Categorical construction versus external interpretation.** The subsection is not wholly internal to `B`. The construction of `A`, the inference functor, its initial algebra, images, and the fiber/algebra comparison takes place in `B` and its slices. The opening formulas `W` and `Ax` are numerical presentations; `Gamma_e` is explicitly an external set of sentences, defined by truth in the standard structure `N` (lines 19–33). The functor `J:P_PA→B` and the specified isomorphism `v` connect those presentations to categorical objects (lines 35–63). A standard number `e` enters the category through the named numeral morphism `epsilon_e:1→E` (lines 126–130). The later graph formula `Prov` is explicitly extracted from a represented categorical morphism (lines 304–333). Finally, the independence conclusion is external: it is proved for standard indices using a structure `K models Gamma_e`, standard truth sets, and the interpretation functors `F_N` and `G_N` (lines 395–413). These are stated transitions, not silent identification of a set with an object of `B`. No unmarked change of framework was found. The section should not be described as a proof conducted entirely inside `B`, nor does it claim an internal subobject of consistent presentations. Its external numerical and semantic application is distinct from Appendix A's categorical construction.

| Data or assertion | Declared types and checked law | Result |
| --- | --- | --- |
| Inclusion and total category, lines 6–17 | `I:S_PA→Split(S_PA)` has `I(X)=(X,1_X)` and `I(f)=f`; `E=I(omega)` is an object of `B=Tot(Split(S_PA))`; `G_N:B→Set`. Identities and composition are inherited by the inclusion. | Pass |
| Predicate presentation, lines 35–63 | `J:P_PA→B`; `r_0:D→Top`, `r_1:D→Sent`, `a:A_0→D` are predicate-category arrows; `v=<Jr_0,Jr_1>:J(D)≅E×S`; `i=vJ(a)`. The graph formulas use the PA single-sort and primitive-recursive abbreviation conventions of §5. | Pass |
| Initial algebra, lines 100–109 | `mathfrak P` is an `H_E`-algebra, with carrier the slice object `(P^all,c^all)` and structure map `alpha:H_E(P^all,c^all)→(P^all,c^all)` in `B/F_E`. It is not identified with its carrier. | Pass |
| Image and range, lines 110–124 | `c:P→E×S`, `m:T→E×S` are total arrows of `B`; `r:E×S⇀T` is partial in `Split(S_PA)`. Both `mr` and `ran(c)` have type `E×S⇀E×S`. Lemma A.7 applies to the partial inverse supplied by Lemma 5.3. | Pass |
| Slice equivalence, lines 157–191 | `Xi_e:B/F_E→B/Fm × B/(E_{≠e}×Fm)`; morphisms are induced pullback arrows, with identity and composition laws justified by uniqueness. `Psi_e` has the reverse type and the stated coproduct object and morphism actions. | Pass |
| Complementary rule data, lines 193–217 | `s_n:R_n^{≠e}→R_n^E`, `t_n:R_n^{≠e}→E_{≠e}`, `rho_n:R_n^E→E`; `p_n^{≠e}` and `q_n^{≠e}` have the required codomains, including `n=0`. | Pass |
| Natural isomorphism, lines 218–250 | `zeta:Xi_e H_E⇒(H_e×H_{≠e})Xi_e`; both components have explicit slice types, and both sides of the stated naturality equation have source `Xi_e H_E(Q,q)` and target `(H_e×H_{≠e})Xi_e(Q',q')`. The check uses arbitrary slice arrows, not only isomorphisms. | Pass |
| Algebra equivalence, lines 252–276 | `Lambda_e:Alg(H_E)→Alg(H_e)×Alg(H_{≠e})`; the structure arrow is `Xi_e(delta) zeta^{-1}` and the morphism action has underlying arrows `(f_e,f_{≠e})`. Naturality turns the algebra-morphism equation into the required equation in each factor. | Pass |
| Initial-algebra comparison, lines 278–301 | Initiality is asserted and proved in algebra categories. The isomorphism is explicitly in `Alg(H_e)`; the underlying slice carrier is then identified separately. Sentence pullback and regular image follow through the algebra isomorphism. | Pass |
| Program index and graph, lines 304–333 | `a_c∈N` is a program index, `G_{a_c}` its arithmetic graph formula, and `gamma_c:P_0→D` the predicate-category morphism. Neither the index nor the formula is treated as a morphism without the stated representation. | Pass |
| Partial computation and total parameterization, lines 358–393 | `a_ell∈I(omega×omega,omega+omega)`; `ell=[a_ell]_PA`; `tau_PA(g×1)=b^{-1}ell` in `S_PA`; `I(g):E→E` and `theta:E→S` in `B`. All displayed composites have matching endpoints. | Pass |
| Semantic conclusion, lines 395–413 | `e,n∈N`, `K models Gamma_e`, `F_N(ell):N×N⇀N amalg N`, and `(G_N q)(e)` is a sentence code. The assertion concerns the decoded sentence, not the code as an object-language formula. | Pass |

The potentially false general principle “arbitrary pullback preserves initial algebras” is not invoked. A Set test with two parameter values also confirms why a binary-rule summand cannot accept children with different parameters: its pullback requires both to equal the parameter of the rule instance. The slice and algebra functors act on arbitrary morphisms, so the ordinary two-object, one-arrow variance test produces no contravariance or isomorphism-only defect.

# (E) Acceptance conditions, non-negotiable

No repair is outstanding for the local acceptance gate. The verifiable endpoints for this cycle are:

1. **§7.2 family construction:** well-typed rule maps for Lemma 5.8 and an initial algebra with its full algebra structure displayed. Satisfied at lines 65–109. Failure would block the family construction.
2. **Proposition 7.5:** an explicit numeral decomposition, typed slice/algebra equivalences, and a proof that the relevant component is initial. Satisfied at lines 151–301. Failure would require dropping the asserted identification with the separately constructed theory fibers.
3. **Family theorem predicate:** fixed numerical parameter/conclusion coordinates and PA-provable equality with the fiber predicate. Satisfied at lines 35–63 and 304–333. Failure would block the stated use of the predicate in Theorem 7.6.
4. **Theorem 7.6:** one PA-represented search and one total parameterization, with independence proved for each standard consistent presentation. Satisfied at lines 344–413. Failure would require withdrawing that theorem in its present form.

These endpoints concern the current text only. No new condition is imposed for a mathematical distinction already supplied by a cited definition or lemma.

# (F) Not checked / uncertainty log

Read in full: frozen §7.2. Read for the dependency checks: the predicate-category construction and Lemmas 5.2–5.3, the construction and proof of Lemma 5.8, Theorem 5.9, the numerical coding and parameterized Turing property in §5, the interpretation functors and standard-code soundness proposition in §6, §7.1's definitions and Lemmas 7.1–7.2, and Appendix A's inference functor, image theorem, sentence-theory construction, and image/range interface. The current PDF text on pages 31–35 was inspected for agreement and anchors.

This review does not re-prove the entire first-order substitution realization, the whole manuscript's categorical preliminaries, the cosheaf results, or the ultrapower theorem. It does not independently verify the primary literature, novelty, a Lean development, or a fresh compilation. Those are not missing premises in the scoped proof; they limit the scope of this audit. No citation or literature claim has been added.

**Strongest confirmed blocker:** none in the reviewed section and inspected interfaces.

**Strongest suspected unconfirmed blocker:** none identified; no conjectural objection is being promoted to a finding.

**Most important thing not checked:** the full first-order syntax and substitution realization underlying the imported soundness theorem was not re-audited constructor by constructor in this cycle.

**Dependence on unavailable material:** the local disposition does not depend on unavailable manuscript material. It uses the explicit earlier lemmas as described above.

**Final recommendation:** unknown for a whole-paper publication decision; **PASS for this scoped review of §7.2**, with no outstanding correction.
