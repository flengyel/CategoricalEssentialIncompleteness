# Explicit types and dependencies after the subsection split

**Round 1 disposition: the mathematical and categorical type checks pass; one local terminology correction remains.** No formula, arrow, hypothesis, or proof step needs a mathematical change. At §7.3, source line 15, replace “family proof predicate” with “provability predicate.” The formula `Prov(e,z)` existentially quantifies the proof code and expresses provability of sentence code `z` from presentation `e`; it is not a relation whose displayed arguments include a proof code.

The reviewed frozen files are:

- `tmp/split25/round1/08a-uniform-theories.tex`, SHA-256 `1b9540d2537f6de7f658e8881d3fc9fc9c47971c1323df775762bbb20efcee45`;
- `tmp/split25/round1/08b-uniform-independent-sentences.tex`, SHA-256 `92580c86b303e4b1e394d1045c953cad4a22e91cf4c637a16b6420e05dd19d99`.

The review concerns §§7.2–7.3 of version 25 of *Logical consequence and essential incompleteness in recursion categories*. Source-line anchors below refer to those files separately. The compiled labels identify §7.2 on page 31 and §7.3 and Theorem 7.6 on page 35. This is an independent source and dependency audit, not a Lean check or a whole-paper certification.

## Single purposes and preservation of the mathematics

Section 7.2 constructs the indexed derivation and theory family, proves its numeral-fiber comparison (Proposition 7.5), and supplies the numerical predicate representing the family image. The concluding predicate paragraph is part of the representation of that same family. It does not begin the independence argument.

Section 7.3 has one conclusion: Theorem 7.6 constructs a total morphism assigning an independent sentence to each consistent standard presentation. Its search program, total parameter map, and semantic contradiction are steps toward that conclusion. It explicitly imports the family, its objects, and its predicate from §7.2. No definition or proof has been stranded on the wrong side of the split.

A literal comparison with the version-24 baseline found only the new subsection heading and label, the replacement of “above” by the named §7.2 reference and object types in the theorem statement, and the added import of `Prov(e,z)` at the beginning of the proof. The remainder of the theorem and proof is unchanged. The containing arithmetic file inputs the family file before the independent-sentence file. The theorem label is preserved, and its number remains 7.6.

## Type inventory for the family construction

| §7.2 lines | Data | Types and checked distinctions |
| --- | --- | --- |
| 6–17 | `B`, `I`, `E`, `S`, `Fm`, `j`, `G_N` | `B=Tot(Split(S_PA))`; covariant `I:S_PA→Split(S_PA)` has explicit object and arrow actions. `E=I(ω)`, `S`, and `Fm` are objects of `B`; `j:S↪Fm` is total. `G_N:B→Set` is the total interpretation. The definition of `I` does not assert that images of arbitrary partial arrows are total. |
| 19–33 | `Ax_PA`, `W`, `Ax`, `Γ_e`, `A_Γ_e` | The first three are formulas in PA's declared single numerical sort. `e∈N` is an external index; `Γ_e` is an external set of sentences. `A_Γ_e↪S` is a subobject represented by the specified formula `Ax(e-bar,z)`. Formula, sentence, code, set, and categorical subobject are distinguished. |
| 35–63 | `J`, `Top`, `D`, `A_0`, numerical projections, `r_0`, `r_1`, `v`, `a`, `A`, `i` | `J:P_PA→B` is the named equivalence. The three carrier predicates are objects of `P_PA`. `π_0^num,π_1^num:N→N` are numerical functions. `r_0:D→Top`, `r_1:D→Sent`, and `a:A_0↪D` are explicitly represented arrows of `P_PA`. `v:J(D)≅E×S` is fixed by those projections; `A=J(A_0)` and `i=vJ(a):A↪E×S` belong to `B`. This does not identify the two categories. |
| 65–80 | `L`, `R_n`, `λ`, `p_n`, `q_n`, `F_E`, `R_n^E`, nullary arrows | All these objects and maps belong to `B`. `λ:L→Fm`, `p_n:R_n→Fm^n`, `q_n:R_n→Fm` for `n=1,2`; `F_E=E×Fm`; `R_0^E=(E×L)+A`, `R_n^E=E×R_n`. Both copairing legs of `q_0^E:R_0^E→F_E` have target `F_E`. `p_0^E:R_0^E→1` is the terminal arrow. |
| 82–93 | `u_n`, `v_n`, `π_nk`, `d_n`, `p_n^E`, `q_n^E` | Their endpoints and index ranges are displayed. The component maps of `d_n:E×Fm^n→F_E^n` repeat the same parameter in every premise. The composites yield `p_n^E:R_n^E→F_E^n`, `q_n^E:R_n^E→F_E`. Finite powers use Appendix A's product conventions, including `X^0=1` and `f^0=1_1`. |
| 94–109 | `H_E`, `Pfrak`, `P^all`, `c^all`, `α` | `H_E:B/F_E→B/F_E` is the inference endofunctor instantiated from the typed rule data. Its object and morphism action is defined in Appendix A. `Pfrak` is an algebra, `(P^all,c^all)` its slice carrier, `c^all:P^all→F_E` its conclusion map, and `α:H_E(P^all,c^all)→(P^all,c^all)` its structure morphism in the slice. These are not conflated. |
| 110–124 | `P`, `c`, `T`, `m`, `r`, `t` | `c:P→E×S` and its regular-image monomorphism `m:T↪E×S` are total maps in `B`. `r:E×S⇀T` is partial in `Split(S_PA)`; `rm=1_T`, `mr=bar(r)=ran(c)=t` are well typed. `t:E×S⇀E×S` is explicitly in the splitting category. |
| 126–148 | `ε_e`, `!_X`, `k_e^X`, `ι_e`, `c_Γ_e` | For external `e∈N` and `X∈B`, `ε_e:1→E`, `!_X:X→1`, and `k_e^X:X→E×X` are total maps. `P_Γ_e` and `c_Γ_e:P_Γ_e→S` have the §7.1 definitions. `ι_e:P_Γ_e→P` is in `B`. The proposition's four-arrow square has matching endpoints. |
| 151–191 | `E_≠e`, `u_e`, `k_≠e^X`, `Ξ_e`, `Ψ_e`, slice arrows | `E_≠e∈B`, `u_e:E_≠e↪E`, and `[ε_e,u_e]:1+E_≠e≅E` give the declared decomposition. `k_≠e^X:E_≠e×X→E×X`. `Ξ_e:B/F_E→(B/Fm)×(B/(E_≠e×Fm))` and its reverse quasi-inverse `Ψ_e` have object and morphism actions. Pullback uniqueness proves functor laws; coproduct decomposition supplies the equivalence. The component arrows `f_e` and `f_≠e` have their slice types stated. |
| 193–217 | `F_≠e`, `π_E`, `ρ_n`, `R_n^≠e`, `s_n`, `t_n`, complementary rules, `H_≠e`, `H_e` | `F_≠e=E_≠e×Fm`; `π_E:F_E→E`; `ρ_n:R_n^E→E`; `s_n:R_n^≠e→R_n^E`, `t_n:R_n^≠e→E_≠e` are pullback arrows. The equations determine `p_n^≠e:R_n^≠e→F_≠e^n` and `q_n^≠e:R_n^≠e→F_≠e`. `H_≠e` and `H_e` have their respective slices as both source and target. |
| 218–250 | `ζ`, `ζ^0`, `ζ^1` | `ζ:Ξ_eH_E⇒(H_e×H_≠e)Ξ_e` is between covariant functors with the same source and target. Its components have explicit slice types. Both paths of the displayed naturality equation run from `Ξ_eH_E(Q,q)` to `(H_e×H_≠e)Ξ_e(Q',q')`. The pullback construction gives naturality for arbitrary slice arrows. |
| 252–295 | `Λ_e`, `δ`, algebra arrow `a`, underlying arrow `f`, `Pfrak_e`, `Pfrak_≠e`, `Qfrak` | `Λ_e:Alg(H_E)→Alg(H_e)×Alg(H_≠e)` is typed. Its object action is conjugation of structure by `ζ`, with the correct inverse direction. Its arrow action is the pair of underlying pullback arrows. Algebras, structure maps, and underlying slice objects are explicit. The resulting isomorphism is in `Alg(H_e)`; the underlying carrier is stated separately. |
| 297–333 | Sentence fibers, `P_0`, `u`, `γ_c`, `a_c`, `Prov` | Pullback along `j` and stable images give the sentence fiber. `u:J(P_0)≅P` is in `B`; `γ_c:P_0→D` in `P_PA` satisfies `J(γ_c)=v^(-1)cu`. `a_c∈N` is the chosen program index. `Prov(e,z)` is an arithmetic provability predicate representing the image in the specified numerical coordinates. |

The category memberships and totality in this table are declarations from the subsection or from the explicitly referenced definitions, not inferred repairs of undeclared data.

## Type inventory for uniform independence

| §7.3 lines | Data | Types and checked distinctions |
| --- | --- | --- |
| 6–19 | `Γ_e`, `E`, `S`, `B`, `q`, `G_N`, `Prov`, `θ`, `Θ` | The statement names §7.2's family and types `E,S∈B=Tot(Split(S_PA))`. It seeks a total `q:E→S` in `B`. `(G_Nq)(e)` is a numerical sentence code, and the conclusion concerns the decoded sentence. The proof explicitly imports `Prov`, `θ:E→S`, and `Θ:N→N`. |
| 20–28 | `C`, `C'`, `R`, `Neg` | `C,C',R` are arithmetic formulas. `Neg:N→N` and its graph-abbreviation convention are defined with `Θ` in §7.1. Composing these numerical functions inside a formula uses that explicit convention, not an unmarked categorical evaluation. |
| 30–44 | `a_ℓ`, `G_aℓ`, `ℓ` | `a_ℓ∈I(ω×ω,ω+ω)` is an index. The graph formula has a proved inclusion in `R` and a proved exact domain. `ℓ=[a_ℓ]_PA:ω×ω⇀ω+ω` is a partial arrow in `S_PA`. The text does not claim that `R` is functional for all parameters. |
| 46–62 | `τ_PA`, `b`, `h`, `g`, diagonal and pairing | `τ_PA:ω×ω⇀ω`, `h:ω⇀ω+ω` are partial source arrows. `b:ω→ω+ω` is an isomorphism; `g:ω→ω` is total in `S_PA`. Both sides of the parameterization equation and of the subsequent diagonal identity have explicit matching source and target. |
| 64–85 | `I(g)`, `q`, `e`, `n`, `K`, `F_N(ℓ)`, `D_i` | `I(g):E→E` is total, and `q=θI(g):E→S` belongs to `B`. `e,n∈N` are external numbers; `K⊨Γ_e` is an external first-order structure. `F_N(ℓ):N×N⇀N⊔N` is a partial function, with literal product/coproduct carriers from §6's recursive interpretation. `D_i⊆N` are the previously defined diagonal domains. |

The inclusion `I` and interpretation functors remain the §7.2 and §6 functors; splitting the exposition does not change their scope or meaning. The predicate `Prov` crosses the subsection boundary through the newly explicit reference. There is no dependency on a symbol whose declaration was removed by the split.

## Composition and universal-property checks

- `vJ(a)` has path `A→J(D)→E×S`; `(1_E×j)i` has path `A→E×S→F_E`; `d_n(1_E×p_n)` has path `R_n^E→E×Fm^n→F_E^n`.
- The partial inverse equations have paths `T→E×S⇀T` and `E×S⇀T→E×S`. The regular-image identification and the range identification use the two different, explicitly named ambient categories.
- `ρ_ns_n=u_et_n` has common type `R_n^≠e→E`. The complementary premise equation has common type `R_n^≠e→F_E^n`; for `n=0` both sides are the unique arrow to `1`. The conclusion equation has common type `R_n^≠e→F_E`.
- `Ξ_e(δ)ζ^(-1)` has path `(H_e×H_≠e)Ξ_e(Q,q)→Ξ_eH_E(Q,q)→Ξ_e(Q,q)`. Naturality transforms the source algebra-morphism equation into both target equations. Full faithfulness then transfers algebra arrows. For essential surjectivity, a pair of target structures can be placed on a carrier in the image of `Ξ_e` through its stated quasi-inverse, conjugated by `ζ`, and lifted uniquely by full faithfulness. This uses the supplied equivalence data; it requires no new preservation assertion about initial algebras.
- The initial pair is tested against `(Qfrak,Pfrak_≠e)`. Pairing two proposed first-component maps with the second component's identity proves uniqueness. Thus the first component is initial in `Alg(H_e)`.
- `v^(-1)cu` has path `J(P_0)→P→E×S→J(D)`. The chosen `v` fixes the parameter and conclusion coordinates. Equality of the fiber subobjects over the fixed sentence object gives PA-provable equivalence of their carrier predicates. Both predicates imply `Sent`, so the universal quantifier over all numerical `z` is valid.
- `τ_PA(g×1)=b^(-1)ℓ` has type `ω×ω⇀ω`. Precomposition by the total `⟨1,g⟩:ω→ω×ω` gives `hg=ℓ⟨1,g⟩:ω⇀ω+ω`; the equality is an equality of partial arrows, including domains. Finally `q=θI(g)` has type `E→S` in `B`.

Lemma 5.8 applies to the family with `F=F_E`, `T=PA`, and `N=2`; it allows arbitrary finite rule data of the displayed types. The fiber argument uses the numeral's decidable complement, not a claim that arbitrary base change preserves initial algebras. The final diagonal argument uses consistency only for the chosen standard parameter. Completeness supplies a model of `Γ_e`; standard-code soundness makes the two proof polarities disjoint in `N`. Every PA axiom belongs to the family presentation. Hence the diagonal-domain lemma supplies the opposite polarity at the selected number, giving the stated contradiction. No assumption `N⊨Γ_e` or reflection of consistency from the interpretation to the source category is used.

## Framework and scope

The derivation, fiber, and image constructions are categorical. The presentations and numerical application explicitly use external natural numbers, sets of sentences, and models. The transitions occur through the named predicate equivalence `J` with its fixed comparison maps, or through `F_N` and `G_N`. No unmarked substitution of sets for categorical objects, of algebras for their carriers, or of formulas for their codes was found.

I inspected the split sources and the relevant predicate-category, initiality, interpretation, soundness, diagonal, finite-power, and inference-functor definitions and proofs. This audit does not recheck every theorem of Appendix A, every bibliography entry, or the entire manuscript. No Lean elaboration or proof checking has been performed. The report's only requested correction is the local replacement of “proof predicate” by “provability predicate”; the types and mathematics otherwise pass their stated scope.
