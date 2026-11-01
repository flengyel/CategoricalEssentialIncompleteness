# Type inventory of §7.2, version 23

This is a source-level inventory of `sections/08a-uniform-theories.tex`, with the definitions in §§5–7.1 and Appendix A consulted. Line references below are to the immutable version 23 source in `tmp/review24/baseline`. The mathematical argument is coherent, but the section does not yet meet the user's requirement that all types and changes of presentation be explicit.

## Findings requiring correction

1. **The numerical presentation of the conclusion morphism is not fixed (lines 174–185).** The equivalence with the predicate category does not by itself specify the coding of the codomain. To use the output code `⟨e,z⟩` in the uniform provability predicate, the codomain isomorphism must be the product isomorphism given by the fixed pairing projections. Choose a predicate `P₀` and an isomorphism `u:J_PA(P₀)→P`; let `D(w)` be the paired predicate for `E×S` and `v:J_PA(D)→E×S` its specified product isomorphism. The index must represent `v⁻¹cu`, not an unspecified presentation of `c`. An arbitrary isomorphism of the codomain could permute the parameter coordinates. This is missing comparison data, not a counterexample to the intended theorem.

2. **The slice equivalence is only partially described (lines 109–113, 129–132).** Its category signature and first component are stated, but the second inclusion and the action on morphisms are unnamed. Name the complement inclusion `κ_e:E_{≠e}→E`, put `l_e=κ_e×1_Fm`, and define `Ξ_e` by the pair of pullbacks along `k_e^Fm` and `l_e`, on objects and on morphisms. A quasi-inverse sends the pair `x:X→Fm`, `y:Y→E_{≠e}×Fm` to the copairing `[k_e^Fm x,l_e y]:X+Y→E×Fm`, and sends `(f,g)` to `f+g`. Finite extensivity supplies the comparison isomorphisms.

3. **The natural comparison has no named components or naturality equation (lines 124–148).** The displayed natural isomorphism has the right functors, and the pullback argument is valid. For explicit typing, give it a name `ζ:Ξ_eH_E⇒(H_{A_{Γ_e}}×H_{≠e})Ξ_e`, specify that its components are pairs of slice isomorphisms, and state the naturality equation for a declared slice morphism. The summands denoted `B_n` belong to three different rule systems; distinguish them by superscripts or an explicit convention.

4. **Algebras are identified with their carriers without a declared convention (lines 150–165).** The symbols `P_e`, `P_{≠e}`, and `Q` are first used as objects of algebra categories, then as carriers, while their conclusion maps and algebra structures are suppressed. The induced algebra functor should be stated: it sends `((Q,q),δ)` to the algebra with structure `Ξ_e(δ)ζ_(Q,q)⁻¹`, and sends an algebra morphism `f` to `Ξ_e(f)`. Use distinct symbols for algebras and their carriers, or explicitly state the convention before using it. The initial-pair argument itself is valid once these types are supplied.

5. **Several local maps lack explicit declarations.** Name the nullary premise morphism `p_0^E:R_0^E→1` (lines 41–44); state the component range `1≤k≤n` and the projection types in the definition of `d_n` (lines 46–48); write `!_X:X→1` in `k_e^X` (lines 76–79); name the complement inclusion and its copairing with the numeral point (lines 100–108). The unique terminal map and finite-product notation are established in Appendix A, so this needs declarations, not new proofs of their properties.

6. **The search morphism's graph is discussed without a program representative (lines 218–224).** In this category a morphism is an equivalence class of indices. Choose `a_ℓ∈N`, write the two PA-provable graph assertions with `G_{a_ℓ}(⟨e,x⟩,z)`, and then define `ℓ=[a_ℓ]_PA` with its declared source and target. If the assertion about “each interpretation” is retained, quantify a model `M⊨PA` and a parameter `a∈|M|`; otherwise restrict the branch assertion to the standard interpretation used in the subsequent proof. This does not require repeating the proof-search lemma.

No confirmed false theorem or missing existence hypothesis was found. The corrections above make the existing construction and proof explicit.

## Complete inventory

Status **E** means explicitly typed in the section; **D** means defined with its type in a cited or earlier passage; **I** means its type is currently inferred or its presentation is suppressed and needs the correction identified above. Ordinary arithmetic variables range over the object language of first-order arithmetic; their standard interpretations range over `N`.

| Lines | Symbol or expression | Mathematical type | Status and check |
| --- | --- | --- | --- |
| 6–9 | `B=B_PA` | Total category `Tot(Split(S_PA))` | D: definition in §7.1 and §5. |
| 7–8 | `I` | Covariant restriction functor `S_PA→Split(S_PA)`, `I(X)=(X,1_X)`, `I(f)=f` | Signature E; object action on `ω` E; general action D from restriction splitting. State `I(f)=f` locally if requiring every action here. |
| 8–9 | `E` | Object of `B`, namely `(ω,1_ω)` | E. |
| 9 | `G_N` | Covariant functor `B_PA→Set` | D: §6.2. Its value at `E` is `N` with the chosen identity splitting. |
| 10–16 | `Ax_PA`, `W`, `Ax`, `G`, `Sent` | Arithmetic formulas; `Ax_PA,Sent` unary, `W,Ax` binary, `G` ternary | E for definitions, D for `G,Sent`. Distinguish formulas from internal subobjects. |
| 18–24 | `e`, `Γ_e` | Standard natural-number index and external c.e. set of arithmetic sentences | E. `Γ_e` is not an object of `B`; its axiom object is `A_{Γ_e}`. |
| 23–30 | `A_{Γ_e}↪S`, `i:A↪E×S` | Monomorphisms in `B` | E/D. Chosen predicates are specified; no extensional replacement of those formulas is allowed in the categorical fiber argument. |
| 32 | `j:S↪Fm` | Monomorphism in `B` | E; category D from the realization. |
| 33–35 | `L`, `λ:L→Fm` | Object and morphism in `B` representing logical axiom instances | E/D: Appendix A.5 supplies formula and parameter objects; §5 realizes them in `B`. |
| 34–35 | `R_n,p_n,q_n`, `n=1,2` | Objects and morphisms `p_n:R_n→Fm^n`, `q_n:R_n→Fm` in `B` | E/D. |
| 36–40 | `F_E,R_0^E,R_n^E` | Objects of `B` | E by products/coproducts of the declared objects. |
| 41 | Nullary premise map | `p_0^E:R_0^E→1` in `B` | I: map is described but not named/typed in a formula. |
| 44 | `q_0^E` | `R_0^E→F_E` in `B` | E. Its copairing legs have domains `E×L` and `A`, and common codomain `E×Fm`. |
| 47–48 | `d_n` | `E×Fm^n→(E×Fm)^n` in `B` | E. The component maps have type `E×Fm^n→E×Fm`. Projection signatures and range `1≤k≤n` should be declared. |
| 51–52 | `p_n^E,q_n^E` | `R_n^E→F_E^n` and `R_n^E→F_E` | E; displayed compositions are composable. |
| 57–59 | `H_E` | Covariant endofunctor of `B/F_E` | E; object/morphism construction D from Appendix A.4. This construction should be cited rather than reproved. |
| 60–64 | Initial derivation algebra | An algebra `δ_E:H_E(P^all,c^all)→(P^all,c^all)` in `B/F_E` | I: carrier and conclusion map E; structure map is not named. |
| 65 | `c:P→E×S` | Pullback conclusion morphism in `B` | E. It is obtained along `1_E×j:E×S→E×Fm`. The other pullback leg is not used until the fiber proof; if used, it must be named. |
| 66–74 | `m:T↪E×S`, `t=ran(c)` | Regular-image monomorphism in `B`; restriction idempotent `E×S⇀E×S` in `Split(S_PA)` | E/D. The partial inverse of `m` has type `E×S⇀T`; the current text does not name it. |
| 76–79 | `ε_e`, `k_e^X`, `!` | `ε_e:1→E`; `k_e^X:X→E×X`; `!_X:X→1`, all in `B` | First two E; terminal map D but its subscript is suppressed. |
| 83–85 | Pullback derivation algebra | An `H_{A_{Γ_e}}`-algebra in `B/Fm` | I: the proof supplies the transported structure, but neither its map nor its carrier/conclusion is named here. |
| 86–95 | `P_{Γ_e}`, `c_{Γ_e}`, `ι_e` | Objects of `B`; `c_{Γ_e}:P_{Γ_e}→S`; `ι_e:P_{Γ_e}→P` | E/D: `P_{Γ_e}` and `c_{Γ_e}` defined in §7.1. The displayed square is correctly typed. |
| 96 | `(k_e^S)^*T` | Pullback subobject of `S` in `B` | E/D. It should be understood as the pullback of `m`, not an inverse image of an untyped object. |
| 101–104 | `E_{≠e}` and inclusion | Object `(ω,[x≠ē]_PA)` of `B`; monomorphism `κ_e:E_{≠e}→E` | Object E; inclusion I. Name it, and specify `[ε_e,κ_e]:1+E_{≠e}→E` as the claimed isomorphism. |
| 108–113 | `Ξ_e` | Covariant equivalence `B/(E×Fm)→B/Fm×B/(E_{≠e}×Fm)` | Signature E, complete actions I. The product of categories needs parentheses or an unambiguous convention; the displayed intended grouping is recoverable. |
| 115–118 | Restricted rule objects | Pullbacks of `π_Eq_n^E:R_n^E→E` along `κ_e` | I: projection map and restricted rule maps are described without names. State their types or give a defined restriction construction. Nullary premise codomain remains `1`. |
| 121–123 | `H_{≠e}` | Covariant endofunctor of `B/(E_{≠e}×Fm)` | Signature E; rule construction needs the preceding typed restrictions. |
| 126–128 | Natural isomorphism | `ζ:Ξ_eH_E⇒(H_{A_{Γ_e}}×H_{≠e})Ξ_e` | Functors compose correctly. Components/naturality I; see finding 3. |
| 129–133 | `(Q,q)`, `(Q_e,q_e)`, `(Q_{≠e},q_{≠e})` | Objects of the three respective slice categories | E. `Q≅Q_e+Q_{≠e}` is an isomorphism in `B`, compatible with the structure map over `E×Fm`. |
| 134–143 | `B_n` summands | Objects of `B` with conclusion maps to the respective formula bases | D from Appendix A, but overloaded across three endofunctors. Distinguish the rule systems explicitly. |
| 144–148 | Commutation with slice morphisms | Naturality of the component pullback isomorphisms | Valid by uniqueness, but the maps/equality are not displayed. |
| 150–156 | Algebra-category equivalence | `Alg(H_E)→Alg(H_{A_{Γ_e}})×Alg(H_{≠e})` | Source and target E; action and transported structure I. |
| 157–165 | `(P_e,P_{≠e})`, `Q`, `P_e→Q`, `1_{P_{≠e}}` | Algebras/algebra morphisms in two different algebra categories, with underlying slice maps in different slices | I: current carrier notation suppresses conclusion and structure maps. The product-initiality argument is correct for explicitly declared algebra objects. |
| 167–171 | Sentence restriction and image pullback | Pullbacks in `B`, followed by regular-image stability | Correct. This uses Appendix A by reference and does not reprove its closure result. |
| 174–180 | `P_0,a_c` | Unary Σ₁ formula and standard program index `a_c∈N` | I: formula/index kinds are understandable, but the source and target presentation isomorphisms must be fixed. Exact-domain formula is correct after doing so. |
| 184–194 | `Prov`, specialization and `Prov_{Γ_e}` | Binary and unary arithmetic Σ₁ formulas; PA-provable universal equivalence | E/D once the pairing codomain is fixed. The equivalence is stronger than agreement in `N`, and follows from the identified subobjects in the predicate presentation. |
| 199–202 | `q:E→S` | Morphism of `B`; underlying total set function `G_Nq:N→G_NS` | E. Independence is asserted for standard externally consistent presentations. |
| 205–210 | `θ`, `Θ`, `Neg`, `C,C′` | `θ:E→S` in `B`; primitive-recursive numerical code functions; arithmetic binary formulas | E/D. Use definitional equivalence for `C,C′` to distinguish formula definitions from categorical equality. |
| 215–221 | `R`, `ℓ` | Ternary arithmetic Σ₁ formula; partial morphism `ω×ω⇀ω+ω` in `S_PA` | Signature E; graph representative and input/output coding should be explicit. |
| 222–224 | Interpreted graph | Partial function on `|M|×|M|` with values in two tagged copies of `|M|`, decoded from its numerical graph | I: model and parameter types are unquantified in this sentence. The later proof uses only `M=N`. |
| 226–229 | `g`, `τ_PA`, `b` | Total `g:ω→ω`; `τ_PA:ω×ω⇀ω`; isomorphism `b:ω→ω+ω`, all in `S_PA` | `g` E, other types D from §7.1. The equation has common source `ω×ω` and target `ω`. |
| 231–235 | Pairings, diagonal, `h` | `⟨1,g⟩:ω→ω×ω`; `g×1:ω×ω→ω×ω`; `Δ_ωg:ω→ω×ω`; `h:ω⇀ω+ω` | Maps compose correctly. `h` was previously defined only as a composite; its arrow type should be stated under the strict requirement. The final equation has type `ω⇀ω+ω`. |
| 237 | `q=θI(g)` | Total composite `E→E→S` in `B` | Correct. `I(g):E→E` belongs to `B` because `g` is total. |
| 239–243 | `e,n,K` | Standard `e,n∈N`; nonempty first-order model `K⊨Γ_e` | E/D. Completeness supplies the model; standard-code soundness concerns codes in `N` and satisfaction in this separate `K`. |
| 244–250 | Branch values, `D_0,D_1`, conclusion code | Elements of interpreted coproduct; subsets of `N` from §7.1; element of `G_NS⊆N` | Correct once the graph representative/interpretation is explicit. The identity `G_NI(g)=F_Ng` for total `g` follows from the chosen extension/restriction of the interpretation functor. |

## Suggested codomain presentation

Let `Top(x)≡(x=x)`, so that `J_PA(Top)=E`, and use the chosen sentence object `S=J_PA(Sent)`. Let

\[
D(w)\equiv\exists e\exists z\,
 (w=\langle e,z\rangle\land\operatorname{Sent}(z)).
\]

In `P_PA`, define `r_0:D→Top` and `r_1:D→Sent` by the graphs

\[
D(w)\land e=\pi_0(w),\qquad D(w)\land z=\pi_1(w),
\]

where `π_0,π_1` are the numerical pairing projections. Then

\[
v=\langle J_{\mathrm{PA}}(r_0),J_{\mathrm{PA}}(r_1)\rangle:
J_{\mathrm{PA}}(D)\xrightarrow{\cong}E\times S
\]

is the product isomorphism. For an isomorphism `u:J_PA(P_0)→P`, choose the program index for `v⁻¹cu`. The support and totality equations in §5 give the exact-domain formula, and the range formula then has the declared pair coordinates. This supplies the missing comparison without repeating Appendix A.

## Scope and conclusion

The inspected claims are the family derivation construction, its numeral fibers, and the uniform independent-sentence morphism. No whole-paper literature or formalization judgment is made. The numerical coding and predicate equivalence in §5 were consulted, not reconstructed from first principles. No manuscript file was edited by this reviewer. The section requires the explicit presentation, functor, and algebra declarations above before it can pass this specific type audit.
