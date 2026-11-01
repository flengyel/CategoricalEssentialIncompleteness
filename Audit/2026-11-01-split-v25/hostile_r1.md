# (A) Kill-shots / hard blockers

None established. The mathematical constructions and arguments in the split subsections pass the checks described below. One local terminology correction remains before the editorial gate is closed.

This is an independent author-side audit of version 25 of *Logical consequence and essential incompleteness in recursion categories*, §7.2, “An indexed family of arithmetic theories,” and §7.3, “Uniform independent sentences.” The frozen sources are `tmp/split25/round1/08a-uniform-theories.tex` and `tmp/split25/round1/08b-uniform-independent-sentences.tex`. Their SHA-256 hashes are respectively `1b9540d2537f6de7f658e8881d3fc9fc9c47971c1323df775762bbb20efcee45` and `92580c86b303e4b1e394d1045c953cad4a22e91cf4c637a16b6420e05dd19d99`. Section 7.2 occupies printed/PDF pages 31–35; §7.3 occupies page 35. Source line anchors below name the relevant file. Earlier review dispositions were not used as evidence.

# (B) Major weaknesses

None confirmed in these subsections or their inspected dependency interfaces.

The principal mathematical checks were:

1. **Family existence, §7.2 lines 65–124, p.32.** The rule data have types `p_n^E:R_n^E→F_E^n` and `q_n^E:R_n^E→F_E` in `B`, including `p_0^E:R_0^E→1`. The cited Lemma 5.8 permits an arbitrary object `F` and arbitrary finite rule data, so it applies with `F=E×Fm`, `N=2`. It supplies the complete initial algebra, not only a carrier. The sentence pullback and regular image are formed in `B`; the partial inverse and range are explicitly in `Split(S_PA)`. The image theorem is applied with its actual hypotheses. **Evidence: structural argument and inspected earlier proof. Result: pass.**

2. **Numeral fibers, Proposition 7.5, pp.33–34.** The decidable numeral decomposition `1+E_{≠e}≅E` gives the displayed slice equivalence. Every premise and conclusion of a rule has the same parameter. Consequently the rule pullbacks decompose through that equivalence, and the components of `zeta` are isomorphisms. Its displayed naturality identity has matching source and target. The algebra structure is transported in the correct direction by `Xi_e(delta) zeta^(-1)`. The induced functor on algebras is fully faithful, and the quasi-inverse on carriers supplies the structures needed for essential surjectivity. Initiality of the first component follows by testing the product initial object against `(Q,P_{≠e})` and pairing any competing maps with the second component's identity. No general assertion that arbitrary base change preserves initial algebras is used. **Evidence: derivation. Result: pass.**

3. **Numerical coordinates, §7.2 lines 35–63 and 304–333, pp.32,34–35.** The product isomorphism `v:J(D)≅E×S` is determined by the numerical projections. Thus the presentation of the conclusion map cannot silently permute the parameter or sentence coordinates. The composite `v^(-1)cu:J(P_0)→J(D)` is well typed; fullness of `J` and the functional-search lemma supply a representing graph with the specified exact domain. Its image predicate is precisely `Prov(e,z)`. The fiber result identifies subobjects over the fixed `S=J(Sent)`, so the predicate-category description gives the asserted PA-provable equivalence with `Prov_{Γ_e}`. Both predicates imply `Sent`, which justifies the universal quantifier over all numerical `z`. **Evidence: derivation from the explicit presentation. Result: pass.**

4. **Uniformity and independence, Theorem 7.6, §7.3 lines 30–85, p.35.** One arithmetic relation `R(e,x,z)` supplies one index and one partial morphism `ell:omega×omega⇀omega+omega`. The relation need not be functional for inconsistent presentations; the first-witness search still has the asserted graph inclusion and exact domain. Parameterized computation yields one total `g:omega→omega`. The displayed precomposition identity gives `hg=ell<1,g>` as an equality of partial arrows, including their domains. Hence `q=theta I(g):E→S` is total in `B`. For a consistent standard presentation, a model `K` and standard-code soundness make the two predicates disjoint. At `n=F_N(g)(e)`, either predicate sends the self-application to the opposite diagonal domain, and Lemma 7.1 yields the other predicate. This is a contradiction. Every PA sentence axiom is available by the definition of the family. Neither `N models Γ_e` nor reflection of target soundness into source consistency is assumed. **Evidence: derivation. Result: pass.**

# (C) Minor issues

**H1 — Use “provability predicate,” not “family proof predicate.”**

- **Anchor:** §7.3, p.35, `08b-uniform-independent-sentences.tex`, lines 15–16: “Use the family proof predicate `Prov(e,z)` of Section 7.2.”
- **Claim as written:** the formula `Prov(e,z)` is called a proof predicate.
- **Failure mode:** ambiguous terminology; minor exposition issue.
- **Why the wording should change:** its arguments are a theory index `e` and a sentence code `z`. The derivation variable has already been existentially quantified in §7.2, lines 319–323. The formula therefore expresses provability in the indexed presentation, whereas “proof predicate” commonly denotes a relation involving the code of a particular proof.
- **Evidence:** the displayed definition `Prov(e,z) ≡ exists d G_{a_c}(d,<e,z>)` and the following equivalence with `Prov_{Γ_e}(z)`.
- **Repair:** replace the opening phrase by “Use the provability predicate `Prov(e,z)` of”.
- **Downstream impact:** no formula, theorem, type, or argument changes. The correction preserves the distinction between a derivation code and the assertion that such a code exists.
- **Severity and repairability:** minor; one local phrase. This does not invalidate Theorem 7.6, but it should be corrected under the user's standard-terminology requirement.

No additional necessary correction was identified. In particular, the use of “inference endofunctor” imports its definition from Appendix A; it is not a substitute for unspecified data.

# (D) Cross-section consistency failures

No mathematical dependency is lost by the split. The two subsections have distinct purposes:

- **§7.2:** construct the arithmetic derivation and theory family, prove its numeral-fiber characterization, and give its numerical provability predicate. The predicate at the end represents the same family and belongs to this construction.
- **§7.3:** use that family predicate to construct the total uniform sentence morphism and prove independence for each consistent standard presentation.

Theorem 7.6 now names §7.2 in its statement, and the proof expressly imports its predicate. Lemma 7.1 supplies `theta` and the numerical function `Theta`; §7.1 supplies `Neg`, `D_0`, and `D_1`. The split does not turn any previously bound proof variable into a free variable. The theorem numbers and labels remain attached to the same statements.

| Interface | Explicit types and laws checked | Result |
| --- | --- | --- |
| Source and splitting | `I:S_PA→Split(S_PA)`, `I(X)=(X,1_X)`, `I(f)=f`; `B=Tot(Split(S_PA))`; `E=I(omega)` | Covariant inclusion; an arbitrary `I(f)` is not asserted total. |
| Presentation | `J:P_PA→B`, `v:J(D)≅E×S`, `u:J(P_0)≅P`, `gamma_c:P_0→D` | The equivalence and its comparison isomorphisms are kept distinct from literal equality. |
| Rule objects | `R_n^E∈B`, `p_n^E:R_n^E→F_E^n`, `q_n^E:R_n^E→F_E` | All arities and product projections are declared. Appendix A's finite-power convention covers `n=0`. |
| Initial algebra and carrier | `mathfrak P=((P^all,c^all),alpha)` with `alpha:H_E(P^all,c^all)→(P^all,c^all)` in `B/F_E` | Algebras, slice objects, and underlying objects are distinguished. |
| Slice comparison | `Xi_e:B/F_E→B/Fm×B/F_{≠e}`; reverse functor `Psi_e`; induced pullback and coproduct actions | Object and arbitrary-morphism actions are stated; uniqueness of pullback maps gives the functor laws. The check is not restricted to isomorphisms. |
| Natural isomorphism | `zeta:Xi_e H_E⇒(H_e×H_{≠e})Xi_e` | Component slice types and the naturality equation are explicit. Both sides of that equation have the stated common source and target. |
| Algebra comparison | `Lambda_e:Alg(H_E)→Alg(H_e)×Alg(H_{≠e})` | The structure-map and morphism actions have the correct variance. `Xi_e(delta)zeta^(-1)` is composable. |
| Image and partial range | `c:P→E×S`, `m:T↪E×S` in `B`; `r:E×S⇀T`, `t:E×S⇀E×S` in the splitting category | `rm`, `mr`, and `ran(c)` have the displayed endpoints. |
| Numerical graph and program | `a_c∈N`, arithmetic formula `G_{a_c}`, predicate-category map `gamma_c`; `a_ell∈I(omega×omega,omega+omega)` and `ell=[a_ell]_PA` | Indices, formulas, and represented morphisms are separately typed. |
| Uniform computation | `tau_PA:omega×omega⇀omega`, `b:omega≅omega+omega`, `g:omega→omega`, `h:omega⇀omega+omega` in `S_PA` | `tau_PA(g×1)=b^(-1)ell` and `hg=ell<1,g>` are well typed; totality is asserted only for the appropriate maps. |
| Interpretation | `G_N:B→Set`; `F_N:S_PA→Pfn`; `q:E→S` | `F_N(omega×omega)=N×N` and `F_N(omega+omega)=N amalg N` follow from §6's recursive object definition. The final value is a sentence code. |

The family and fiber constructions are categorical constructions in `B`, its slices, and algebra categories. External `e∈N`, sentence sets `Γ_e`, graph formulas, and first-order models are expressly introduced for the numerical presentation and application. The passages to and from categorical data use `J`, the displayed comparison isomorphisms, the numeral morphisms, `F_N`, and `G_N`. No unmarked substitution of a set for a categorical object was found. It would be inaccurate to describe the whole application as being conducted without external numerical or model-theoretic reasoning.

As a variance test, a general slice arrow `f:(Q,q)→(Q',q')` induces arrows in the same direction in both pullbacks. The naturality identity makes the algebra equation pass to their images in the same direction. No reverse arrow is required. A two-parameter Set interpretation of a binary rule also shows why children with different parameters cannot belong to a rule summand: both premise parameters must equal the rule parameter.

# (E) Acceptance conditions, non-negotiable

1. **Close H1 in §7.3:** replace “family proof predicate” by “provability predicate” and verify the final source. Failure does not reject the theorem mathematically, but leaves the requested terminology review unfinished.
2. **Preserve the explicit split interface:** the §7.3 statement must refer to the family and objects of §7.2, and its proof must use the predicate constructed there. This endpoint is already satisfied. Losing it would require repairing the section before acceptance.
3. **Preserve the categorical and numerical distinctions:** retain the typed comparison isomorphisms, algebra structure maps, source partial maps, and stated interpretation functors. This endpoint is already satisfied. Losing these data would reopen the relevant construction or typing objections.

No major reconstruction or additional theorem is required by this audit. A final check after H1 is corrected is sufficient to close the identified finding, provided the rest of the reviewed source is unchanged.

# (F) Not checked / uncertainty log

Read completely: both frozen subsections. Read for dependency verification: the predicate-category construction and functional-search lemma; regularity, finite extensivity, and numerical image descriptions; the general derivation initial-algebra proof; the arithmetic coding and parameterized computation; the interpretation functors; standard-code soundness; §7.1's diagonal and proof-search statements and proofs; and Appendix A's inference functor, image theorem, and finite-product conventions. The compiled PDF text and labels were inspected for the subsection boundaries and anchors.

This audit does not reprove all the first-order syntax and substitution realization, all categorical preliminaries, the cosheaf application, or the ultrapower results. It introduces no literature or novelty claim and performs no new primary-source verification. It does not certify that a Lean development contains these results, or that their formalization will have no further obligations. No formalization was run.

**Strongest confirmed blocker:** none mathematical; H1 remains a local terminology correction.

**Strongest suspected unconfirmed blocker:** none identified.

**Most important thing not checked:** the complete underlying syntax/substitution realization was not re-audited constructor by constructor in this cycle.

**Dependence on unavailable material:** no unavailable manuscript material is needed for the scoped conclusions.

**Final recommendation:** unknown for a whole-paper publication decision. For the named subsections, the mathematics and explicit types pass; local review closure awaits the single wording correction H1.
