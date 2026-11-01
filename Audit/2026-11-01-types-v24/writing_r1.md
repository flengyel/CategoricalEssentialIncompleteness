# Mathematical-writing review, second round: explicit types

The revised text has removed the earlier unnecessary terminology, but it does not yet meet the requested standard that every type and passage between categories be explicit. The remaining difficulties occur chiefly where the proof moves from a slice category to its algebra category, and from a categorical morphism to a numerical graph formula. These are local presentation defects; no false theorem is established by them.

The manuscript reviewed is *Logical consequence and essential incompleteness in recursion categories*, version 23. The full target is §§6–7, with particular attention to §7.2. Anchors refer to the immutable source in `tmp/review24/baseline/`: **06** means `sections/06-interpretation-in-models.tex`, **08** means `sections/08-essential-incompleteness-of-arithmetic.tex`, and **08a** means `sections/08a-uniform-theories.tex`. Printed page numbers agree with PDF page numbers.

The governing source consulted is Knuth, Larrabee, and Roberts, *Mathematical Writing*, Stanford course report, §1, printed pp. 1–6, in the supplied `tmp/review_sources/klr.txt`. Points 5, 10–11, 14, 17, and 26 concern self-contained statements, connected exposition and definitions, consistent notation, unambiguous reading, and unnecessary jargon. The requirement that all types be displayed is the user's instruction and the mathematical-writing skill's supplementary convention; it is not attributed verbatim to KLR.

## Actual outline

| Location | Function | Main dependencies |
| --- | --- | --- |
| §6 opening and §6.1 | Interpret program graphs and lift complementary conditionals. | Coding identities in §5; restriction structure and lifting theorem. |
| §6.2 | Define the total interpretation and prove finite-limit, coproduct, and image preservation. | Predicate category and its equivalence with the total splitting. |
| §6.3 | Prove semantic substitution and soundness on finite standard derivations. | Realized syntax and substitution; Appendix A's axiom and rule morphisms. |
| §6.4 | Compare ultrapowers of the standard interpretation with interpretation in the arithmetic ultrapower; transport the soundness factorization. | Łoś's theorem, preservation properties, naturality. |
| §7.1 | Represent diagonal domains, construct a partial proof-search map, and apply the comparison theorem. | §§3–6 and finite PA computation proofs. |
| §7.2 opening | Form a family of axiom, derivation, and consequence objects over the presentation-index object. | General derivation-algebra realization and Appendix A's image theorem. |
| Proposition 7.5 | Identify numeral fibers by decomposing slices and algebra categories. | Complemented numeral inclusion, finite extensivity, natural comparison of inference functors. |
| Theorem 7.6 | Construct one total morphism selecting an independent sentence for every consistent standard presentation. | Exact-domain search, Turing parameterization, soundness, diagonal-domain representation. |
| §7.3 | Realize syntax and derivations in the numerical recursion category's total splitting. | Recursive evaluation of finite syntax and proofs; Appendix A. |
| §7.4 | Describe numeral instances under theory inclusion and compare with Bernardi's numerical argument. | The numerical realization and inseparability. |

This order supports the proof dependencies. No reorganization is recommended.

## Required local repairs

| Anchor | Difficulty | Concrete repair |
| --- | --- | --- |
| 08a:32–63, p. 31–32 | The imported rule data are said to come from Appendix A, where their ambient category is an arbitrary category. Their realization in the present category and the initial algebra's structure map are not declared here. The nullary premise map is described without a symbol. | State once that the realized objects and morphisms in this construction belong to `B=Tot(Split(S_PA))`, citing Theorem 5.9. Write `p_0^E:R_0^E→1`. Name the initial algebra as an algebra object, with its structure map `α:H_E(P^all,c^all)→(P^all,c^all)` in `B/(E×Fm)`. No constructor proof need be repeated. |
| 08a:46–48, p. 31 | The component number and the projections in the definition of `d_n` have implicit ranges and endpoints. | State `1≤k≤n`; declare the two projections from `E×Fm^n` and `π_k:Fm^n→Fm`, or give the component equation with these types in one sentence. This is a local instance of the user's explicit-type requirement, not an allegation that projection notation is nonstandard. |
| 08a:71–79 and 100–116, p. 32 | The partial inverse of `m`, the terminal map in `k_e^X`, and the complementary inclusion are unnamed. The proof then refers to “the parameter of its conclusion” rather than the corresponding map. | Write `r:E×S⇀T` in `Split(S_PA)` with `rm=1_T`, `mr=bar r=ran(c)`; declare `!_X:X→1`; name `u_e:E_{≠e}↪E` and set `ρ_n=π_E q_n^E:R_n^E→E`. Define the restricted rule objects as pullbacks of `ρ_n` along `u_e`, with their premise and conclusion maps explicitly typed. These definitions instantiate the appendix; they do not repeat its proofs. |
| 08a:108–148, p. 32–33 | The source and target of `Xi_e` are given, but its action on morphisms is suppressed. The natural isomorphism is unnamed and its component types and naturality equation must be reconstructed. | Define `Xi_e(Q,q)=((Q_e,q_e),(Q_{≠e},q_{≠e}))` and `Xi_e(u)=(u_e,u_{≠e})`, with the latter maps induced by the two pullback squares. Name the comparison `ζ:Xi_e H_E⇒(H_{A_{Γ_e}}×H_{≠e})Xi_e`, give a component's source and target, and state the naturality equality for a typed slice morphism. Preserve the existing pullback-pasting argument as its justification. |
| 08a:150–165, p. 33 | `P_e`, `P_{≠e}`, and `Q` stand for whole algebras in one sentence and their carrier objects in the next. The morphisms used in the uniqueness argument have no declared category. | Use distinct symbols for complete algebras, for example `𝔓_e`, `𝔓_{≠e}`, and `𝔔`, or explicitly declare that the symbols denote whole algebras throughout this paragraph. Type the unique arrow in the product of algebra categories, and its components as algebra morphisms. To make the induced equivalence explicit, state that an algebra structure is transported as `Xi_e(α) ζ^{-1}`, and an algebra morphism is sent to its two pullbacks. |
| 08a:174–194, p. 33 | The exact-domain equation is now explicit, but “under the predicate presentation” still suppresses the input and output presentation isomorphisms. An arbitrary presentation of `E×S` does not by itself mean that its numerical coordinates are `⟨e,z⟩`. | Fix the output predicate `D(w)=Sent(π_1 w)` (the `E` coordinate is unrestricted), a pairing-induced isomorphism `v:J_PA(D)≅E×S`, an input presentation `u:J_PA(P_0)≅P`, and a graph representing `v^{-1} c u:P_0→D`. Then choose `a_c` for that graph. This makes the later formula `G_{a_c}(d,⟨e,z⟩)` explicitly refer to the intended output coordinates. |
| 08a:218–224, p. 33 | A morphism is said to have a graph implying the arithmetic relation `R`, without naming the representative graph. “On each interpretation” leaves both the model and its parameter unspecified. | Choose `a_ℓ∈I(ω×ω,ω+ω)`, set `ℓ=[a_ℓ]_PA`, and state the PA-provable implication `G_{a_ℓ}(⟨e,x⟩,z)→R(e,x,z)` and the domain equivalence with `C(e,x)∨C′(e,x)`. If the following modelwise assertion remains, quantify `M⊨PA` and `a∈|M|`, and type the interpreted partial function. Alternatively, state only the standard interpretation needed in the proof. |
| 06:205–222, p. 25, semantic substitution | `x` and `a` have no declared sets. The tuple `(φ,x,t)` mixes decoded formulas/terms with the standard interpretation of a categorical subobject, whose components are codes. The final decoding sentence acknowledges the distinction but does not type the membership assertion. | Declare `x∈N` and `a∈|K|`. State the condition as “`t` is free for `x` in `φ`,” citing the realization proposition, or explicitly use the tuple of codes `(⌜φ⌝,x,⌜t⌝)` in the image of the interpreted admissibility inclusion under the canonical finite-product comparison. Do not identify a formula with its code silently. |
| 08:62–79 and 151–158, pp. 29–30 | The diagonal map `h`, idempotents `a_0,a_1`, numerical functions `Θ,Neg`, and interpreted proof-search map `s_Γ` have implicit endpoints. | Give `h:ω⇀ω+ω`, `a_i:ω⇀ω` in `S_PA`; give `Θ,Neg:N→N`, with `Θ` taking values in the sentence-code subset; and give `s_Γ:F_Mω⇀F_Mω+F_Mω` in `Pfn`. The existing formulas remain their definitions. |
| 06:413–433, p. 27, comparison lemma | The naturality argument is correct in substance, but the arbitrary comparison component `η_B` is defined only by a composite, and the morphism under the naturality claim is not displayed. | Give `η_B:U(G_NB)→G_MB`. For `f:B→B′` in `B_PA`, state `G_M(f)η_B=η_{B′}U(G_N(f))`. The already supplied full-faithfulness argument proves this equality; no new proof of Łoś's theorem is required. |

The first five findings directly concern the categorical fiber proof. The sixth and seventh concern the transition to numerical predicates and back to categorical morphisms. The last three are related omissions in the preceding sections and should be corrected in the same pass.

## Definition-order and terminology audit

The principal objects are introduced in an appropriate order. `E`, `A`, the family rule objects, its derivation object, its sentence pullback, and its image precede the fiber proposition. The uniform provability predicate precedes the independent-sentence theorem. The standard interpretation and its ultrapower comparison precede their applications.

The core terms regular image, finite extensivity, slice category, initial algebra, restriction splitting, partial inverse, and ultrapower are standard. They should remain. “Predicate presentation” is defined in §5 and is legitimate, but invoking it alone does not fix an arbitrary object's chosen numerical coordinates. “Family” and “fiber” describe ordinary categorical constructions here; no new technical terminology is needed.

The type distinctions that must remain visible are:

- an object of `B`, an object of `B/F`, and an algebra for an endofunctor of `B/F`;
- a morphism of `S_PA`, its image under the inclusion into `Split(S_PA)`, and its interpretation as a partial function;
- a decoded formula or term, its numerical code, and a point of an interpreted syntax object;
- an arithmetic graph formula and the morphism represented by that formula;
- canonical isomorphism of chosen pullbacks and literal equality of their carriers.

The new numerical equality and representation formulas in version 23 are useful and should be retained. The semantic substitution and numerical realization proofs perform work not done in Appendix A. The categorical numeral-fiber proof likewise establishes a new base-change fact; it must not be deleted as repetition.

## Suggested formulation for the algebra-category passage

The precise choice of symbols can follow the rest of the section. The essential distinction can be expressed as follows:

```latex
Write $\mathfrak P=((P^{\mathrm{all}},c^{\mathrm{all}}),\alpha)$
for the initial $H_E$-algebra. Let
$(\mathfrak P_e,\mathfrak P_{\ne e})$ be its image under the
displayed equivalence of algebra categories. For any
$\mathfrak Q\in\operatorname{Alg}(H_{A_{\Gamma_e}})$,
initiality gives a unique morphism
\[
 (\mathfrak P_e,\mathfrak P_{\ne e})
 \longrightarrow(\mathfrak Q,\mathfrak P_{\ne e})
\]
in the product of algebra categories. Its first component is an
$H_{A_{\Gamma_e}}$-algebra morphism
$\mathfrak P_e\to\mathfrak Q$. Pairing any two such morphisms
with $1_{\mathfrak P_{\ne e}}$ proves their equality. Hence
$\mathfrak P_e$ is initial.
```

This uses the same mathematical argument and avoids identifying an algebra with its carrier without a convention.

## Scope and status

All three target source files were read, together with the relevant predicate-category definitions, Turing property, syntax-realization statements, and Appendix A's inference construction. The original KLR source was consulted. PDF text was used for page anchors. No manuscript files were edited by this reviewer, and no revised PDF was compiled or visually inspected in this round.

Status: **the explicit-type review is not yet passed**. The required repairs above are concrete and local. I found no confirmed false theorem in the new material, but this writing review does not certify mathematical correctness or novelty. Once the section is corrected, a second reading should check these distinctions in the revised text rather than repeat the whole review mechanically.
