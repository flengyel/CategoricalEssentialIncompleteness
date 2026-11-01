# Outline, dependencies, and types in the v28 revision

Reviewed sources: `tmp/move28/main.diff`, `tmp/move28/note_revision.diff`, the corresponding complete current passages in `output/manuscript/local_connectedness`, and `output/local_connectedness_note_v1/Ranges_and_Inseparability_v1.tex`. This is an independent check of the revision, not an audit of every unchanged proof in the 77-page paper.

No required mathematical correction was found in the revised comparison corollary, its applications, or the replacement section argument in the note. One local terminology clarification is recommended below.

## Actual revised outline and mathematical functions

| Passage | Mathematical function | Dependencies actually used |
|---|---|---|
| Main §3 opening and summand notation, lines 3–14 | Explain the comparison and name the two restriction idempotents of a binary coproduct. | Restriction coproducts, zeros, ranges and range agreement from §2. |
| Main §3.1, Theorem `thm:comparison`, lines 18–79 | Produce a total source morphism whose interpretation avoids two disjoint target domains. | A source Turing morphism, source coproduct isomorphism, range functor, specified target partial morphism and its source lift. The final noncomplementation conclusion uses the nonzero identity and preservation of one join along the resulting total target morphism. |
| Main §3.1, Corollary `cor:separator`, lines 81–98 | Rule out a lifted target conditional for a complementary target separator. | The comparison theorem, nonzero interpreted identity, and binary-join preservation along total target morphisms. |
| Main §3.2, Corollary `cor:source-conditionals`, lines 102–145 | Deduce source inseparability from total source morphisms with prescribed values on complementary source domains. | Complement preservation by the range functor; range agreement after the copairing of two complementary restrictions; Corollary `cor:separator`. |
| Main §3.2, Proposition `prop:disjoint-joins`, lines 147–164 | Construct those source morphisms from joins of morphisms having disjoint restrictions. | The restriction order, total coproduct injections, and the assumed joins of parallel morphisms. No target structure is used. |
| Main §6, Corollary `cor:model-pair`, lines 103–121 | Apply the source conditional criterion to each interpretation in a model of arithmetic. | Proposition `prop:model`, Lemma `lem:switch`, nonempty model carrier, and preservation of unions by total inverse images in `Pfn`. |
| Main numerical incompleteness subsection, `08d-numerical-incompleteness.tex`, lines 29–51 | Apply the criterion to ordinary partial recursive functions and transport the pair through the numerical equivalence. | Complementary c.e. domains are decidable on the specified carrier; the direct conditional program; the numerical range functor and its nonzero identity. |
| Main Miller application, `04-miller-sequences.tex`, lines 144–183 | Construct representation-independent source conditionals and obtain the Miller diagonal pair. | Exact agreement of the domain and value of each source program across representations, parallel search, coproduct codings, and the range functors `J_p` and `I_p`. Compactness remains in the earlier construction of the Turing morphism, not in the conditional construction. |
| Main Miller application, lines 294–300 | Show that `J_p` does not preserve the specified Turing morphism. | The criterion applied inside `Rec^p` and the displayed `p`-decidable separator of the same pair. |
| Main cosheaf §9.1, lines 151–193 | Construct a conditional on complementary subfunctors and deduce inseparability in the full recursion subcategory. The paragraph following the application records the independent non-equivalence result. | Componentwise c.e. domains, their disjointness and union, coproduct naturality, a computable inverse to the copairing, fullness, and the structure proposition in Appendix B. Local connectedness is recorded but not used for the application. |
| Main cosheaf theory subsection, lines 326–350 | Deduce numerical recursive inseparability at the two endpoint components. | The endpoint Turing property, fullness of `K_2`, numerical conditionals, the underlying-partial-function range functor, and the nonzero carrier. |
| Main Appendix C | Exhibit a faithful, zero-reflecting, product-preserving range functor for which the needed lift fails and the diagonal pair is separable. | The explicitly defined mixed morphism class, acceptable numberings and specialization, the nonrecursive set `A`, and the description of total source morphisms. |
| Main Appendix D, Corollary `cor:pair`, lines 95–123 | Establish inseparability simultaneously in the family of countable models and preserve the pair under consistent theory extension. | The single source conditional of Lemma `lem:switch`, coordinatewise preservation, the faithful family theorem, fullness of the quotient on hom-sets, and preservation of products by that quotient. |

## Outline of the separate note

1. **Introduction.** State the noncomplementation result and the range-functor inseparability result, and give their categorical and arithmetic context.
2. **Restriction categories and recursion categories.** Define restrictions, partiality, coproducts, near products and Turing morphisms; derive the total-index identity needed later.
3. **Ranges and the diagonal domain.** Develop joins, distributivity, direct and inverse images, and prove noncomplementation of the diagonal domain.
4. **Recursively inseparable domains.**
   - Connected domains: give an independent direct-image and coproduct alternative result.
   - Range functors: define preservation and the typed coproduct comparison; give the nonzero-connected-domain consequence for locally connected targets.
   - Sections and weak choice: reduce partial monicity to tests by total morphisms, prove the four-piece coproduct proposition without local connectedness, obtain unique sections by weak choice, and identify their values on complementary domains.
   - Inseparability theorem: combine the typed lift and total-index identity with the target inverse-image join law.
   - Disjoint joins: give a sufficient source construction for the lifting hypothesis.
   - Counterexample: show the lift cannot be suppressed.

The connected-domain subsection and the connected-kernel proposition are now a separate branch of the note. Neither is invoked in the revised section construction or inseparability proof. This is a dependency fact, not a recommendation to delete them.

## Type and inference checks

### Main source conditional corollary

The source morphisms `epsilon_0 ell_c` and `i_0 c'` both have type `U` to `U+U`. Their equalities after `c` and `c'` are composable. Their equalities after `[c,c']:U+U` to `U` therefore follow by the coproduct universal property. The latter copairing has range `c vee c'=1_U`, giving equality by the stated agreement law. Taking restrictions gives exactly `ell_c^* epsilon_0=c'`; the analogous equation has the tags exchanged. The range functor preserves these restrictions and the coproduct comparison transports them to `FU+FU`. All morphisms and restriction idempotents occur on the objects claimed.

### Cosheaf conditional

In `09-three-point-space.tex:157–179`, `m:C` to `V` and `m':C'` to `V` are total natural transformations. Their copairing `q:C+C'` to `V` is natural. The parallel component membership search terminates for every element of `V_j`, because the component domains are disjoint and cover `V_j`; its output is the inverse of `q_j`. From `r_i^V q_0=q_i r_i^{C+C'}`, composition with the component inverses gives the displayed naturality equation. Thus the inverse belongs to the stated total functor category, rather than merely existing componentwise in sets. Finally `[i_1m,i_0m']q^{-1}:V` to `V+V` is a total morphism in that category and belongs to the full source subcategory. No missing gluing or computability step was found.

### Miller conditional

The revised passage at `04-miller-sequences.tex:162–175` explicitly locates `c,c'` in `E_a`. The definition at lines 89–95 supplies one program for each partial identity with the same exact domain for every representation. Dovetailing those programs returns the first tag precisely on the first domain and the other tag precisely on its complement. The returned value and termination are representation-independent. Thus the construction defines a source morphism, not merely a family of oracle-relative morphisms.

### Note section construction

At note lines 664–730, `rho_i:X+X` to `X`, `epsilon_i:X+X` to `X+X`, `e_i,f_j,delta_ij:Y` to `Y`, and `x_ij,y_ij,z_ij:Y` to `X` have consistent endpoints. The morphisms `x_ij`, `y_ij` and `z_ij` are not asserted to be total; the note uses a single `to` notation for all morphisms and defines totality separately at lines 163–165. Distributivity is proved earlier at lines 422–426. The four `delta_ij` have join `1_Y`; their iterated copairing has range `1_Y`, so agreement on the four pieces entails the desired equality. Splitness is then used in Proposition `PropPartialMono` to pass from tests by total morphisms to all tests; weak choice supplies the section. No connected-domain hypothesis is used or silently reintroduced.

### Equality and interpretation

The revised Miller construction uses extensional equality of partial functions, as declared at lines 94–95. The cosheaf construction uses natural transformations and isomorphism classes of partial-map spans, with the subfunctor presentation explicitly justified by Appendix B. The syntactic applications keep the source quotient equality and model interpretation separate; the revised arguments use the already proved source conditional rather than asserting that a target piecewise function is automatically a source morphism. No new conflation of representatives and morphisms was found in the reviewed passages.

## Local clarification recommended

**Anchor:** `sections/09-three-point-space.tex:339–342`, “their switching sections are total recursive maps”.

**Issue:** This phrase retains the old section-based description, but does not name the partial morphism of which the asserted morphisms are sections. The new application needs their values on the complementary restrictions. The construction is mathematically available; the phrase leaves the actual property used implicit.

**Recommended replacement:**

```latex
For complementary restriction idempotents $c,c':W\rightharpoonup W$
in $\mathcal K_2$, run the membership searches for their c.e.\ domains
in parallel. Returning $i_1(w)$ on the domain of $c$ and $i_0(w)$ on
the domain of $c'$ gives a total recursive morphism
$\ell_c:W\to W+W$ satisfying
$\ell_cc=i_1c$ and $\ell_cc'=i_0c'$.
It belongs to $\mathcal K_2$ by fullness.
```

This is a local clarification, not a mathematical blocker or a change to the criterion.

## Scope limits

I independently checked the above typed arguments and their direct dependencies. I did not reverify every unchanged realization proof, the full Miller reduction, the construction of the cosheaf Turing morphism, all external literature attributions, Lean files, or the PDF layout. No whole-paper correctness or novelty judgment is made.
