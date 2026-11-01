# Mathematical Writing review of the split subsections

**Result: one local terminology correction required; no other necessary correction identified.** The new organization gives each subsection one mathematical purpose. Section 7.2 constructs and identifies the indexed family of arithmetic theories, including its numerical provability predicate. Section 7.3 uses that family to prove uniform independence. The change preserves the type declarations and proof dependencies. This report concerns version 25 of *Logical consequence and essential incompleteness in recursion categories*, not a whole-paper review.

Reviewed snapshots:

- `tmp/split25/round1/08a-uniform-theories.tex`, SHA-256 `1b9540d2537f6de7f658e8881d3fc9fc9c47971c1323df775762bbb20efcee45`.
- `tmp/split25/round1/08b-uniform-independent-sentences.tex`, SHA-256 `92580c86b303e4b1e394d1045c953cad4a22e91cf4c637a16b6420e05dd19d99`.

Line numbers below refer to those frozen files. The rendered version 25 manuscript places §7.2 on printed/PDF pages 31–35 and §7.3 on page 35; §7.4 starts on page 36.

## Actual outline and purposes

| Location | Mathematical function | Required inputs and output |
| --- | --- | --- |
| §7.2, lines 4–33 | Fix the ambient category and indexed axiom presentations | Uses the realized syntax in `B=Tot(Split(S_PA))`; defines external presentations `Γ_e` and their internally represented axiom subobjects. |
| §7.2, lines 35–63 | Specify the numerical presentation of the family axiom subobject | Uses `J:P_PA→B` and the numerical pairing to define the fixed product comparison `v:J(D)≅E×S` and monomorphism `i:A↪E×S`. |
| §7.2, lines 65–124 | Construct the family derivation algebra and its sentence image | Applies Lemma 5.8 to the displayed rule data and Appendix A's image theorem. Records the corresponding range idempotent in the restriction splitting. |
| §7.2, lines 126–301 | Identify the numeral fibers | Proposition 7.5 proves that each fiber is the individual derivation algebra and that its sentence image is the generated theory. The proof uses the numeral complement, slice equivalence, natural comparison of inference functors, and induced algebra equivalence. |
| §7.2, lines 304–333 | Give the numerical predicate representing that same family image | Specifies a presentation of the conclusion morphism and derives the PA-provable equivalence with each individual provability predicate. This is the numerical representation of the subsection's constructed object, not a separate independence result. |
| §7.3, lines 4–12 | State the uniform independence theorem | Theorem 7.6 explicitly imports `Γ_e` and `E,S∈B` from §7.2 and states the type and conditional property of `q:E→S`. |
| §7.3, lines 15–65 | Construct the total sentence morphism | Uses the family provability predicate, functional search, and parameterized Turing property. The proof records the partial diagonal identity before defining `q`. |
| §7.3, lines 67–85 | Prove its independence property | For each standard consistent presentation, soundness and the diagonal-domain lemma exclude both proof polarities. |

The split therefore satisfies the user's one-purpose criterion. The dependencies remain in reading order. No additional subsection or reorganization is needed.

## Governing source and comparison

I consulted the supplied Knuth–Larrabee–Roberts *Mathematical Writing*, §1, printed pages 1–5, and the discussions of definitions, notation, audience, and sentence construction in §§4–5, printed pages 9–13. The categorical typing requirements are the user's requirement and the plugin's supplementary conventions, not category-specific rules attributed to KLR.

| Manuscript location | Finding or checked feature | Source principle or independent rationale | Action |
| --- | --- | --- | --- |
| §7.3, p.35, line 15: “family proof predicate” | `Prov(e,z)` has no derivation-code argument: §7.2 defines it by existentially quantifying that code. The established term is “provability predicate.” The formula and its use are otherwise clear. | Independent mathematical terminology requirement; KLR §1 point 14 on consistent notation and point 26 on avoiding unnecessary jargon. | Replace “Use the family proof predicate” with “Use the provability predicate.” |
| §7.2, p.31, lines 4–17 | The opening states the construction's purpose and then its ambient categories and objects. | KLR §1 points 11–13 and 24. | Retain. |
| §7.2, pp.32–34, lines 65–301 | The argument names and types the rule maps, slice functors, natural comparison, algebra structures, and underlying carriers. The prose explains why the comparisons apply. | User's explicit-type requirement; KLR §1 points 10–11,14,17. | Retain the detailed declarations and reasoning. |
| §7.2, pp.34–35, lines 304–333 | The representation of the family image is proved before the subsection ends. The fixed product comparison supplies the numerical coordinate meanings. | KLR §1 points 10–11; preservation of mathematical dependencies. | Retain at the end of §7.2. |
| §7.3, p.35, lines 6–19 | The statement names its imported family and objects; the proof explicitly points to the predicate in §7.2. The former word “above” has been replaced by a precise cross-reference. | KLR §1 point 5, with the contextual qualification in §§4–5 on previously defined data. | Retain. |
| §7.3, p.35, lines 30–65 | Program index, represented partial morphism, total parameter map, and total sentence map have distinct types. The composition identity is derived before application. | User's explicit-type requirement and KLR §1 point 14. | Retain. |
| Both subsections | No empty paragraph, unsupported promotional phrase, editorial-process comment, or other invented terminology was found. Every paragraph defines data, states a result, explains a construction, or proves a step. | KLR §1 points 10–13 and 26; plugin's mathematical-prose requirements. | No other deletion or expansion is warranted. |

The correction to “provability predicate” was independently identified by the hostile reviewer during the parallel review and checked here against the displayed definition. It is a terminology correction, not a newly discovered gap in the theorem.

## Definition order and explicit types

I checked the named definitions in the modular manuscript before classifying notation as missing. In particular:

- §7.2 declares `B`, the inclusion `I:S_PA→Split(S_PA)`, `E=I(ω)`, `S,Fm∈B`, `j:S↪Fm`, and `G_N:B→Set`. It specifies where the finite categorical constructions occur. The object and morphism actions of the interpretation functors are in §6.
- The numerical formulas `Ax`, `D`, and `A_0` are separated from their predicate-category objects and their images under `J`. The graphs of `r_0`, `r_1`, and `a` are written. The chosen product comparison `v` and presentation isomorphism `u` mediate the numerical coordinates. An equivalence of categories is not treated as equality.
- The rule data include the nullary premise map and the arity ranges. Appendix A's finite-power convention covers `n=0` and `n=1`; the powers are finite products. Its definition of the inference endofunctor is imported with all the required data supplied here.
- The initial algebra `mathfrak P`, its underlying slice object `(P^all,c^all)`, and its structure arrow `α` are separately declared. The total sentence conclusion `c`, image inclusion `m`, and partial inverse `r` have their correct ambient categories and endpoints.
- Proposition 7.5 states its parameter range, the initial-algebra conclusion, and a typed pullback square. `P_Γ` and `c_Γ` are defined in §7.1, so their specialized occurrences are not undeclared symbols.
- The functors `Xi_e` and `Psi_e` have source/target categories and object/morphism actions. The natural comparison `ζ` has component types, component categories, and its naturality equation. The induced functor `Λ_e` distinguishes algebra morphisms from their underlying slice arrows. The initiality argument takes place in algebra categories, and the underlying slice object is identified afterward.
- The closing representation argument declares `u:J(P_0)≅P`, `γ_c:P_0→D`, and the type of `v^{-1}cu`. It separates the natural-number index `a_c`, its graph formula, and the represented morphism. The PA-provable fiber equivalence follows from equality of the represented subobjects over the fixed sentence object.
- Theorem 7.6's moved statement explicitly points to §7.2 for `Γ_e,E,S` and states `q:E→S` in the total category. Its proof points to the same subsection for `Prov`. Its references to `θ`, `Θ`, `Neg`, `b`, `h`, `D_0`, and `D_1` are supported by the definitions and graph-abbreviation convention in §7.1.
- The proof declares `a_ell∈I(ω×ω,ω+ω)`, the partial arrow `ell=[a_ell]_PA`, the total arrow `g:ω→ω`, and the total image `I(g):E→E`. The displayed equations have matching sources, targets, and composition directions.
- The final paragraph explicitly uses external `e,n∈N`, a model `K⊨Γ_e`, and `F_N(ell):N×N⇀N⊔N`. It concludes with a numerical code and the corresponding sentence. The passage to sets occurs through the stated interpretations; it is not an unmarked identification of internal objects with sets.

No type declaration or proof step was lost at the new subsection boundary. The proof of the fiber comparison remains in §7.2, while the diagonal argument is confined to §7.3. Appendix A remains used by reference for the general inference-functor and image constructions.

## Required replacement and closure condition

At §7.3, line 15, replace

```latex
Use the family proof predicate $\operatorname{Prov}(e,z)$ of
```

with

```latex
Use the provability predicate $\operatorname{Prov}(e,z)$ of
```

After this replacement, recheck the final snapshot and its rendered boundary. No other wording change is requested by this review.

## Scope

Read in full: both frozen subsections. Inspected for dependencies: the predicate category and search lemma in §5, the general derivation-initiality statement, the interpretation functors in §6, the relevant definitions and diagonal/proof-search results in §7.1, and Appendix A's finite products, inference functor, image theorem, and sentence-theory construction. Consulted the actual KLR source as specified above. Rendered and visually inspected manuscript pages 31–35; no clipping, unresolved reference, or unreadable display was found. The new subsection heading and theorem fit together on page 35.

This editorial review does not certify the whole paper, reverify the literature, or constitute Lean formalization. No new literature claim is proposed. The requested local endpoint is a stable text with explicit types and intelligible proof dependencies; the terminology replacement above is the only outstanding editorial action in round 1.
