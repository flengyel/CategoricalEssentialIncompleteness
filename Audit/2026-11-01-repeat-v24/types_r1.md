# Independent type and dependency audit of §7.2

**Result: PASS for the reviewed section.** No ill-typed expression, missing type declaration, or failed dependency was identified. No manuscript change is recommended by this audit.

The reviewed source is `tmp/review25/round1/08a-uniform-theories.tex`, SHA256 `bcf6666d968ac4a68e6351bf2c1497ee1d86724d8c33dfef26fecaf266f267bd`. This is §7.2, “An indexed family of arithmetic theories,” in version 24 of *Logical consequence and essential incompleteness in recursion categories*. Anchors below are source lines in that snapshot. The review was independent of earlier acceptance reports.

The scope comprises every construction and composition in §7.2, the definitions imported from §§5–7 and Appendix A, and the application of those results. This is not a whole-paper certification, a novelty assessment, or formal verification.

## Ambient categories and interpretation

| Lines | Data | Type and status |
| --- | --- | --- |
| 6–17 | `B`, `I`, `E` | `B = Tot(Split(S_PA))`; `I:S_PA → Split(S_PA)` is covariant, sends `X` to `(X,1_X)` and a partial arrow `f:X⇀Y` to the same representative between those identity splittings. `E=I(ω)` is an object of `B`. The definition does not assert that every `I(f)` is total. |
| 10–17 | `S`, `Fm`, `j`, `G_N` | `S,Fm ∈ B`, `j:S↪Fm` is total; `G_N:B→Set` is the total interpretation functor from §6. The chosen splitting gives `G_N(E)=N`. |
| 19–33 | `Ax_PA`, `W`, `Ax`, `Γ_e`, `A_Γ_e` | The first three are arithmetic formulas in PA's single numerical sort. `e,z,y` are numerical variables, not categorical generalized elements. `Γ_e` is an external set of sentences, whereas `A_Γ_e↪S` is the internally represented axiom subobject. The chosen predicate for each fiber is explicitly `Ax(e-bar,z)`. |
| 36–59 | `J`, `Top`, `D`, `A_0`, numerical projections | `J:P_PA→B` is the previously constructed covariant equivalence. The predicates `Top,D,A_0` are objects of `P_PA`. `π_0^num,π_1^num:N→N` are numerical functions. Their use in arithmetic formulas is covered by the primitive-recursive graph-abbreviation convention in §5. |
| 48–63 | `r_0`, `r_1`, `v`, `a`, `A`, `i` | `r_0:D→Top`, `r_1:D→Sent`, and `a:A_0↪D` belong to `P_PA`, with their graph formulas displayed. `v:J(D)≅E×S` is the product comparison determined by `J(r_0),J(r_1)`. `A=J(A_0) ∈ B`; `i=vJ(a):A↪E×S`. No equivalence of categories is treated as an equality. |

All morphisms in `B` are total by its definition. §7.2 explicitly locates products, coproducts, and pullbacks in `B`. The interpretation `F_N:S_PA→Pfn`, as opposed to `G_N:B→Set`, is used only on source arrows of `S_PA` in the final proof.

## Rules, derivations, and the image

| Lines | Data | Type and status |
| --- | --- | --- |
| 65–71 | `L,R_1,R_2,λ,p_n,q_n` | Objects of `B`; `λ:L→Fm`, `p_n:R_n→Fm^n`, `q_n:R_n→Fm` for `n=1,2`. Their constructor definitions are imported from Appendix A's first-order rules, whose realization was proved in §5. |
| 72–80 | `F_E`, `R_n^E`, `p_0^E`, `q_0^E` | `F_E=E×Fm`, `R_0^E=(E×L)+A`, `R_n^E=E×R_n`. `p_0^E:R_0^E→1`; `q_0^E:R_0^E→F_E`. Both legs of its copairing have target `F_E`. |
| 82–93 | `u_n,v_n,π_nk,d_n,p_n^E,q_n^E` | The projections and the permitted indices `n=1,2`, `1≤k≤n` are explicit. `d_n:E×Fm^n→F_E^n` is specified by all its components. `p_n^E:R_n^E→F_E^n` and `q_n^E:R_n^E→F_E` have the required rule types. |
| 94–109 | `H_E`, `Pfrak`, `P^all,c^all,α` | `H_E:B/F_E→B/F_E` is the covariant inference functor of Appendix A. Its object and morphism actions are explicitly defined there and specialized by the displayed rule data. `Pfrak=((P^all,c^all),α)` is an algebra, its carrier is the slice object `(P^all,c^all)`, `c^all:P^all→F_E`, and `α:H_E(P^all,c^all)→(P^all,c^all)` is a slice arrow. These types remain distinct. |
| 110–124 | `P,c,T,m,r,t` | `c:P→E×S` is the sentence pullback; `m:T↪E×S` is its regular image in `B`. `r:E×S⇀T` and `t:E×S⇀E×S` are arrows in `Split(S_PA)`, with `r` partial. `rm=1_T`, `mr=bar(r)=ran(c)=t` have the correct endpoints. |

Lemma 5.8 applies with `T=PA`, `F=F_E`, `N=2`: it allows arbitrary objects and rule morphisms of these types. It does not require the formula object itself to be `Fm`, nor a separately established preservation of initial algebras by base change. The regularity, finite extensivity, partial inverse of `m`, and extension of ranges to the restriction splitting are all established in §5.3 and its following discussion. Appendix A's least-image theorem supplies exactly the assertion made in lines 113–116.

## Fibers, functors, and algebra transport

| Lines | Data | Type and status |
| --- | --- | --- |
| 126–148 | `ε_e,!_X,k_e^X,ι_e,c_Γ_e` | `e∈N`, `X∈B`, `ε_e:1→E`, `!_X:X→1`; `k_e^X:X→E×X`. `P_Γ_e` and `c_Γ_e:P_Γ_e→S` were defined in §7.1. `ι_e:P_Γ_e→P` is a total `B`-morphism. All four arrows of the proposition's pullback square have explicit endpoints. |
| 151–156 | `E_≠e,u_e,k_≠e^X` | `E_≠e=(ω,[x≠e-bar]_PA)∈B`; `u_e:E_≠e↪E`. The numeral and its decidable complement give `[ε_e,u_e]:1+E_≠e≅E`. `k_≠e^X:E_≠e×X→E×X`. |
| 157–178 | `Ξ_e`, its objects and arrows | Covariant `Ξ_e:B/F_E→(B/Fm)×(B/(E_≠e×Fm))`. It sends `(Q,q)` to the two explicitly typed pullback slice objects and a slice arrow `f:(Q,q)→(Q',q')` to the corresponding induced pullback arrows `(f_e,f_≠e)`. The equations giving a slice arrow and the reason for the functor laws are explicit. |
| 179–191 | `Ψ_e` | Covariant quasi-inverse with its source and target categories displayed. Its value at `(x:X→Fm,y:Y→E_≠e×Fm)` is `[k_e^Fm x,k_≠e^Fm y]:X+Y→F_E`; its arrow value is the explicitly typed coproduct `f+g:X+Y→X'+Y'`. Extensivity supplies the stated natural equivalence isomorphisms. |
| 193–217 | `F_≠e,π_E,ρ_n,R_n^≠e,s_n,t_n,p_n^≠e,q_n^≠e,H_≠e,H_e` | `F_≠e=E_≠e×Fm`; `π_E:F_E→E`; `ρ_n:R_n^E→E`. The pullback arrows `s_n:R_n^≠e→R_n^E` and `t_n:R_n^≠e→E_≠e` are typed, with their commuting equation. `p_n^≠e:R_n^≠e→F_≠e^n` and `q_n^≠e:R_n^≠e→F_≠e` determine `H_≠e:B/F_≠e→B/F_≠e`. `H_e=H_AΓ_e:B/Fm→B/Fm`. |
| 218–250 | `ζ`, `ζ^0`, `ζ^1` | Natural isomorphism `Ξ_e H_E⇒(H_e×H_≠e)Ξ_e` between covariant functors with the same source and product-slice target. Each component has its endpoints and ambient slice stated. The naturality equation has common source `Ξ_e H_E(Q,q)` and target `(H_e×H_≠e)Ξ_e(Q',q')`, as stated. |
| 252–276 | `Λ_e`, algebras, `δ`, algebra arrow `a`, underlying arrow `f` | Covariant `Λ_e:Alg(H_E)→Alg(H_e)×Alg(H_≠e)`. It sends structure `δ:H_E(Q,q)→(Q,q)` to the components of `Ξ_e(δ) ζ_(Q,q)^(-1)`. Algebra arrows are explicitly separated from their underlying slice arrows. Naturality of `ζ` gives their algebra equations, and functoriality follows from that of `Ξ_e`. |
| 278–301 | `Pfrak_e,Pfrak_≠e,Qfrak` and induced maps | The first two are objects of their respective algebra categories; `Qfrak∈Alg(H_e)`. The displayed unique arrow belongs to their product category. Pairing a candidate first-component arrow with `1_Pfrak_≠e` is well typed and proves uniqueness. The resulting initial-algebra isomorphism is explicitly in `Alg(H_e)`, not an equality of carriers. |

The zero-arity case causes no exception: Appendix A declares `X^0=1` and `f^0=1_1`. Thus `(k_≠e^Fm)^0 p_0^≠e = p_0^E s_0` is an equality of the unique arrows `R_0^≠e→1`. For positive arity, a rule's common parameter forces all child conclusions into the same component; the pullback comparisons defining `ζ` therefore exist and are isomorphisms. There are no mixed-parameter rule trees.

The algebra equivalence does not confuse the image of an algebra with the image of its carrier. Given a pair of target algebras, choose a source slice carrier through `Ψ_e`; transport the pair's structure to its `Ξ_e` image, compose with `ζ`, and use full faithfulness of `Ξ_e` to obtain a unique source structure. This proves the essential-surjectivity assertion made in the text. Initiality of the first component follows by testing the product initial object against `(Qfrak,Pfrak_≠e)`, exactly as written. Pulling its unique algebra isomorphism back along `j` yields `ι_e` and the displayed sentence pullback; stable images then give the fiber statement for `m`.

## Numerical theorem predicate and the uniform map

| Lines | Data | Type and status |
| --- | --- | --- |
| 304–318 | `P_0,u,γ_c,a_c` | `P_0` is a Σ₁ predicate and an object of `P_PA`; `u:J(P_0)≅P` belongs to `B`. `γ_c:P_0→D` belongs to `P_PA`; `J(γ_c)=v^(-1)cu:J(P_0)→J(D)`. The standard natural number `a_c` is a program index, not this morphism itself. Its graph represents the predicate-category arrow, and the displayed PA theorem records its precise source domain. |
| 319–333 | `Prov`, `Prov_Γ_e` | Both are arithmetic predicates. The fixed comparison `v` converts the product-coordinate pair `(e,z)` to the numerical code `⟨e,z⟩` used by `G_a_c`. The fiber comparison is equality of subobjects over the fixed `S=J(Sent)`, and hence gives the claimed PA-provable equivalence of their represented predicates. Both predicates imply `Sent(z)` in PA, so the unrestricted quantifier over `z` is valid. |
| 335–357 | `q,θ,Θ,Neg,C,C',R` | The claimed `q:E→S` is a total morphism of `B`. The recalled `θ:E→S` is a total `B`-morphism, and `Θ:N→N`, `Neg:N→N` are primitive-recursive numerical functions from §7.1. The arithmetic formulas `C,C',R` use their declared PA-provably total graph abbreviations. They are not morphisms of `B` at this stage. |
| 358–372 | `a_ℓ`, `ℓ` | `a_ℓ∈I(ω×ω,ω+ω)` is a standard index. The two displayed PA theorems give its graph inclusion and exact domain, not a false functionality assertion for `R`. `ℓ=[a_ℓ]_PA:ω×ω⇀ω+ω` is a partial arrow of `S_PA`. |
| 374–390 | `τ_PA,b,h,g,Δ_ω` | `τ_PA:ω×ω⇀ω`, `h:ω⇀ω+ω` are partial arrows of `S_PA`. `b:ω≅ω+ω` is total invertible; `g:ω→ω` is total; `Δ_ω:ω→ω×ω` is the diagonal. Their displayed composites have the asserted endpoints. |
| 392–413 | `I(g),q,e,n,K,F_N(ℓ),D_0,D_1` | `I(g):E→E` is total, so `q=θI(g):E→S` belongs to `B`. Here `e,n∈N`; `K` is an external first-order model of `Γ_e`. `F_N(ℓ):N×N⇀N⊔N` is a partial function in `Pfn`. `D_0,D_1⊆N` were defined in §7.1. `(G_N q)(e)` is a sentence code, explicitly distinguished from the decoded sentence in the theorem. |

`F_N(ω×ω)=N×N` and `F_N(ω+ω)=N⊔N` are literal consequences of the recursive object definition of `F_M` at the beginning of §6; no unstated preservation isomorphism is required in the last paragraph of §7.2. On total identity-splitting maps, the chosen extension and total restriction give `G_N(I(g))=F_N(g)`.

## Composition checks

Every nontrivial displayed composition has matching intermediate objects:

| Expression | Intermediate type; result |
| --- | --- |
| `vJ(a)` | `A→J(D)→E×S` |
| `(1_E×j)i` | `A→E×S→E×Fm` |
| `d_n(1_E×p_n)` | `E×R_n→E×Fm^n→F_E^n` |
| `π_nk v_n` | `E×Fm^n→Fm^n→Fm` |
| `rm`, `mr` | `T→E×S⇀T`; `E×S⇀T→E×S` |
| `ε_e!_X` | `X→1→E` |
| `k_e^Fm x`, `k_≠e^Fm y` | `X→Fm→F_E`; `Y→E_≠e×Fm→F_E` |
| `ρ_n s_n = u_e t_n` | Both `R_n^≠e→E` |
| `(k_≠e^Fm)^n p_n^≠e = p_n^E s_n` | Both `R_n^≠e→F_E^n`, including `n=0` |
| `k_≠e^Fm q_n^≠e = q_n^E s_n` | Both `R_n^≠e→F_E` |
| The naturality equation for `ζ` | Both `Ξ_e H_E(Q,q)→(H_e×H_≠e)Ξ_e(Q',q')` |
| `Ξ_e(δ)ζ_(Q,q)^(-1)` | `(H_e×H_≠e)Ξ_e(Q,q)→Ξ_e H_E(Q,q)→Ξ_e(Q,q)` |
| `v^(-1)cu` | `J(P_0)→P→E×S→J(D)` |
| `τ_PA(g×1_ω)=b^(-1)ℓ` | Both `ω×ω⇀ω` in `S_PA` |
| `(g×1_ω)⟨1_ω,g⟩=⟨g,g⟩=Δ_ω g` | All total `ω→ω×ω` in `S_PA` |
| `hg=ℓ⟨1_ω,g⟩` | Both `ω⇀ω+ω` in `S_PA`; equality includes the restriction domains |
| `q=θI(g)` | `E→E→S` in `B` |

The parameterized Turing property is applied to `b^(-1)ℓ:ω×ω⇀ω`, so its parameter map has the stated type `g:ω→ω`. Precomposition by the total `⟨1_ω,g⟩` is legitimate for the displayed partial-map equality. It does not claim that `h`, `ℓ`, or `hg` is total.

## Final proof dependencies and outcome

For a standard consistent `Γ_e`, completeness supplies `K⊨Γ_e`. Standard-code soundness and the established fiber isomorphism make the truth sets of `C(e,-)` and `C'(e,-)` disjoint in `N`. This uses no assertion `N⊨Γ_e`. The first-witness program has the prescribed value on each of those two disjoint domains, although its defining relation need not be functional for other parameters. At `n=F_N(g)(e)`, the partial-map identity places `n` in the opposite diagonal domain. Lemma 7.1 then gives the opposite proof predicate because the chosen axiom family contains all chosen PA sentence axioms. Either starting predicate contradicts disjointness. Finally `G_N(q)(e)=Θ(n)` follows from the definitions of `q`, `θ`, and the chosen extension of `F_N`.

There is no assertion about all internal or nonstandard parameters, no internal subobject of consistent indices, and no reflection of target soundness into source consistency. The numerical, categorical, slice, algebra, and semantic types used in this argument remain distinct.

On the author's additional question about set theory: §7.2 is not conducted entirely without a set-theoretic metatheory. It explicitly uses the external natural numbers, the sentence sets `Γ_e`, numerical program indices, and a first-order model `K`. The derivation, fiber, and regular-image constructions themselves take place in `B` and its slice/algebra categories. The passage from numerical presentations to those categories uses `J` with the displayed comparison isomorphisms `v` and `u`; passage to ordinary functions and sets uses `F_N` or `G_N`. No silent identification between an internal object and an external set was found. Thus the construction remains categorical, while its numerical realization and semantic application explicitly use set theory.

**Unresolved findings: none in the stated scope.** No new literature claim was checked or added; no LaTeX compilation or visual-layout validation was performed by this independent type audit.
