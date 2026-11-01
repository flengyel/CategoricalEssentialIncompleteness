# (A) Kill-shots / hard blockers

This audit concerns §§6–7 of *Logical consequence and essential incompleteness in recursion categories*, version 23, with particular attention to §7.2. The sources inspected are the immutable files in `tmp/review24/baseline/sections/`, abbreviated below as **06**, **08**, and **08a**. Relevant definitions in §§2–5 and Appendix A were consulted. The requested acceptance criterion is explicit typing, including distinctions between objects, their presentations, their interpreted sets, and their elements.

No fatal mathematical defect is confirmed. The numeral-fiber proof and the uniform independence proof remain mathematically supported by the stated hypotheses. The section does **not yet meet the requested explicit-type criterion**: several conversions between codes, slice objects, and algebras are still suppressed. These are exhibited below; they are not grounds for claiming that the main theorem is false.

# (B) Major weaknesses

No major mathematical gap is confirmed. The following important inferences were checked independently:

- The rule family is over `E×Fm`, and all premises of an inference have the same parameter as its conclusion. Lemma 5.8 therefore applies to its inference endofunctor.
- A standard numeral inclusion is complemented in the predicate presentation. Finite extensivity decomposes the slice, and the common-parameter property decomposes the inference endofunctor. The resulting equivalence of algebra categories is sufficient to identify the first component of an initial algebra. No preservation of arbitrary initial algebras by arbitrary pullback is assumed.
- The family conclusion morphism has a representing program with its proof predicate as exact domain; this follows from support and totality in Lemma 5.3. The regular-image identification then gives PA-provable equivalence of the specialized theorem predicates.
- The parameterized Turing equation has source `ω×ω` and target `ω`. Precomposing with `⟨1,g⟩:ω→ω×ω` and composing with `b` gives the stated equation of partial maps `ω⇀ω+ω`. Its use at a consistent standard presentation is valid.
- The ultrapower factorization is a composition of total Set-maps. Its argument uses preservation of finite limits and regular images, not preservation of the initial derivation algebra. The model interpreting the axioms remains distinct from the arithmetic model interpreting codes.

# (C) Minor issues

## C1. Decoded expressions are placed in a set of codes

**Anchor:** 06:204–222, p. 25, Lemma 6.5: “For finite terms r,t” and “If (φ,x,t) belongs to the standard interpretation of Adm.” Also 08:41–43, p. 29: “the set G_N P_Γ consists of the finite derivations”; 06:513–515, p. 28: “Each p_i is a standard finite derivation.”

**Failure mode:** `ill_typed` under the literal reading requested by the author. **Severity:** minor, locally repairable. **Evidence:** `structural_argument`: §5 realizes syntax and derivations by numerical carrier predicates; the semantic lemma explicitly speaks of the finite expressions decoded from those carriers. A decoded formula and term are not the numerical codes occurring in the interpreted admissibility subobject. Moreover, `G_N Adm` is the domain of an interpreted monomorphism, rather than literally an already specified subset of the product of code sets.

**Repair:** Let `x∈N` and `a∈|K|` be explicit at assignment update. Express admissibility using the tuple of codes `(⌜φ⌝,x,⌜t⌝)` and the image of the interpreted admissibility inclusion after the canonical product comparison, or define a decoded admissibility relation by that exact map. Say “codes of finite derivations” and “the code of a standard finite derivation” in the two other passages. **Downstream impact:** makes the semantic-substitution statement and the representative description correctly typed; the induction itself remains valid.

## C2. Several family maps have only inferable types

**Anchor:** 08a:32–52, p. 31; 71–79, p. 32; 100–118, p. 32. The nullary premise map is called “the unique map to 1”; the definition of `d_n` uses `π_E`, `π_{Fm^n}`, and `π_k`; the complement inclusion and the map `R_n^E→E` are unnamed.

**Failure mode:** `missing_definition` at the level of the required explicit arrow declarations. **Severity:** minor. **Evidence:** `absence_in_text` for these signatures; their intended signatures follow from the products but are not written.

**Repair:** Declare `p_0^E:R_0^E→1=F_E^0`. Give the two projections of `E×Fm^n` and `π_k:Fm^n→Fm` for `1≤k≤n`, or write an equivalently typed definition of `d_n`. Name the complement inclusion `j_e:E_{≠e}↪E` and the parameter map `ρ_n=π_E q_n^E:R_n^E→E`. If the partial inverse of `m` is used, write its type `r:E×S⇀T` in `Split(S_PA)` and the identity `t=mr`. For `k_e^X`, specify `!_X:X→1`. A standing convention that unqualified objects and arrows in the construction belong to `B` can avoid repeating the category at every elementary arrow.

**Downstream impact:** ensures the displayed family rule maps, restricted rule objects, and range are typed without reconstruction. These additions do not require copying Appendix A's proofs.

## C3. The slice equivalence and natural comparison need explicit actions

**Anchor:** 08a:108–148, p. 32, Proposition 7.5 proof. `Xi_e` is typed, but only its first component functor is stated. The comparison `Xi_e H_E ≅ (H_{A_Γe}×H_{≠e})Xi_e` is unnamed and justified by the phrase “These identifications commute with slice morphisms.”

**Failure mode:** `ambiguous` suppression of functor and natural-transformation data. **Severity:** minor. **Evidence:** `absence_in_text` for the action of `Xi_e` on a slice morphism and for a named component of the natural comparison. The component pullback argument is otherwise correct.

**Repair:** Specify `Xi_e(Q,q)=((Q_e,q_e),(Q_{≠e},q_{≠e}))`, with the second component also a pullback along the named inclusion `j_e×1`. For `f:(Q,q)→(Q',q')`, give `Xi_e(f)=(f_e,f_{≠e})`, where the two maps are induced by pullback. State that the inverse assembles a pair by the coproduct and copairing to `E×Fm`. Name the comparison, for example `κ_e`, give the type of its component at `(Q,q)`, and write its naturality identity. Cite pullback uniqueness for the functor laws and naturality; do not repeat the construction of `H` from Appendix A.

**Downstream impact:** makes the subsequent transport to algebra categories a typed construction rather than an inference the reader must supply.

## C4. Algebra objects are conflated with their carriers

**Anchor:** 08a:150–165, p. 33: “Let (P_e,P_{≠e}) be the image of the initial H_E-algebra” and “For any H_{A_Γe}-algebra Q … a morphism P_e→Q.”

**Failure mode:** `ambiguous`. **Severity:** minor. **Evidence:** `structural_argument`: an algebra here consists of a slice object and a structure morphism. The notation `P_e` previously suggests a carrier in `B`, while the displayed product category has algebra objects. The proof uses algebra morphisms and initiality there, not arbitrary morphisms of carriers.

**Repair:** Name the initial family algebra as a triple `((P^{all},c^{all}),δ)`, with `δ:H_E(P^{all},c^{all})→(P^{all},c^{all})` in the slice. Use a distinct symbol for its transported algebra or display its two full algebra structures. State the algebra equivalence on objects by transporting `Xi_e(δ)` through the inverse of the named comparison component. In the initiality argument quantify over an algebra `((Q,q),α)` and identify the maps as algebra morphisms. The product-initiality argument itself may remain short.

**Downstream impact:** removes the only point where the fiber argument switches between three levels—carrier, slice object, and algebra—without a declared convention. It does not require a second numerical proof of the fiber statement.

## C5. The conclusion index needs a fixed presentation of both endpoints

**Anchor:** 08a:174–187, p. 33: “choose a predicate P_0(d) representing P and an index a_c representing c,” followed by `Prov(e,z)≡∃d G_{a_c}(d,⟨e,z⟩)`.

**Failure mode:** `ambiguous` presentation choice. **Severity:** minor. **Evidence:** `structural_argument`: `c` has endpoints `P` and `E×S` in `B`; `G_{a_c}` is a numerical graph. An equivalence of categories supplies a representation only after presentation isomorphisms are chosen. The output formula uses the specific pairing of the `E` and `S` coordinates, not an arbitrary presentation of the codomain. Exact domain alone does not state this codomain convention.

**Repair:** Give a presentation isomorphism `u_P:J_PA(P_0)≅P` and the product-predicate isomorphism `u_{E,S}:J_PA(D_{E,S})≅E×S`, where `D_{E,S}(w)` is the sentence predicate on the second decoded coordinate. Choose the represented graph so that its image under `J_PA` is `u_{E,S}^{-1} c u_P`, or give the equivalent commuting equation. Then choose `a_c` by the existing graph-representation lemma. The displayed exact-domain and provability formulas follow with the intended coordinates.

**Downstream impact:** ties the uniform predicate to the specified categorical family. The existence of these data is already supplied by Lemma 5.3; no additional existence hypothesis is missing.

## C6. Imported maps can be typed economically at their use

**Anchor:** 06:406–434, p. 27, the naturality argument for `η`; 08:64–80, p. 29, the definitions of `h`, `a_0`, `a_1`, `Θ`, and `Neg`; 08:146–160, p. 30, `s_Γ`; 08a:205–237, p. 33, use of these maps.

**Failure mode:** `ambiguous` suppression of signatures. **Severity:** minor. **Evidence:** `absence_in_text` of the full signatures in the indicated local definitions. Earlier conventions establish enough for the proof to work, but the user's stronger criterion asks that these types be explicit.

**Repair:** State `h:ω⇀ω+ω` and `a_i:ω⇀ω` in `S_PA`, the numerical types of `Θ` and `Neg`, and `s_Γ:F_Mω⇀F_Mω+F_Mω` in `Pfn`. In Lemma 6.8 write naturality as `G_M(f)η_B=η_C U(G_N(f))` for `f:B→C` in `B_PA`, with both sides typed from `U(G_N B)` to `G_M C`. In §7.2 refer to these declarations; duplicating their constructions is unnecessary. A formula such as `C(e,x)` remains an arithmetic formula, not a categorical arrow, and should be described as such.

**Downstream impact:** makes the interpretation, diagonal calculation, and proof-search comparison composable directly from the text.

# (D) Cross-section consistency failures

The code/expression switches in C1 and the carrier/algebra switches in C4 remain from the preceding version and were not exposed by the earlier, less exhaustive typing review. The prior statement that no fatal or major defect was found does not establish that all types were explicit. This audit does not downgrade any previously confirmed mathematical blocker; none was recorded in the inspected v23 reports.

The distinction between `S_PA`, `Split(S_PA)`, and its total subcategory is otherwise maintained. In particular, `q=θ I(g)` is the correct composition: `g` belongs to the syntactic category while `θ` has a split sentence object as codomain. The chosen predicate category is not declared equal to `B_PA`. No internal subobject of consistent presentation indices is asserted. Independence remains a statement about externally consistent standard presentations.

Appendix A supplies the inference functor, the least closed image theorem, and the range/image comparison. The new numeral-fiber argument is a separate application and should remain. Semantic substitution and numerical realization are also application proofs, not repetitions of the appendix.

# (E) Acceptance conditions, non-negotiable

1. **Codes and decoded expressions:** make the semantic admissibility statement and proof-family representatives typed as specified in C1. Endpoint: no finite expression is asserted to belong literally to a numerical carrier. Failure prevents passing the explicit-type review; it does not refute soundness.
2. **Family arrow declarations:** provide the types and category conventions in C2. Endpoint: the source, target, and ambient category of each newly used family arrow can be read from the text. Failure prevents passing the explicit-type review.
3. **Slice and natural-transformation data:** state the actions and component/naturality types in C3. Endpoint: the natural comparison is a transformation between two declared functors, with a stated naturality equality. Failure leaves the algebra transport insufficiently explicit.
4. **Algebra/carrier distinction:** implement C4. Endpoint: the initiality argument is explicitly an argument in the product of the two algebra categories. Failure prevents passing the type review.
5. **Numerical presentation compatibility:** implement C5. Endpoint: a commuting equation links the graph chosen for `a_c` to `c`, with the codomain pairing fixed. Failure leaves the uniform predicate's coordinates implicit.
6. **Imported signatures:** implement C6 or give precise references to already explicit signatures. Endpoint: every interpretation and diagonal composite has declared endpoints. Failure prevents passing the requested review, although the underlying constructions remain supported.

No theorem needs to be dropped on the present evidence. The same revised section should be checked against these conditions. Passing this local criterion is not a whole-paper mathematical certification or a publication recommendation.

# (F) Not checked / uncertainty log

The three assigned source files were read, together with the relevant conventions in §§2–5 and Appendix A. The v23 PDF was used for page locations. No new compilation or rendering was performed by this agent. The low-level compiler proofs of §5 were consulted as dependencies rather than reconstructed instruction by instruction. No new literature or novelty assessment was attempted.

Strongest confirmed blocker to the requested local pass: the expression/code and carrier/algebra distinctions in C1 and C4 are not explicit. Strongest suspected unconfirmed mathematical blocker: none found. Most important thing not checked: the fully revised source after these changes and its rendered layout. The findings do not depend on unavailable manuscript material. Final recommendation: **unknown** as a whole-paper publication judgment; **not yet passed** for the stated explicit-type criterion.
