# Mathematical Writing review of the numerical realization

**Disposition: revision required.** The intended numerical realization has a recognizable proof, but the current subsection does not meet the author's requirements of one mathematical purpose and explicit categorical types. Its universal-property proofs and comparison functors omit data that should be displayed before formalization. These are identifiable exposition and typing obligations; this review does not assert that Proposition 7.7 is false.

Manuscript: *Logical consequence and essential incompleteness in recursion categories*, version 25, §7.4, “The numerical realization,” printed/PDF pages 36–38. The frozen source is `tmp/numerical26/round1/08-essential-incompleteness-of-arithmetic.tex`; source-line anchors below refer to that file. I read lines 285–488 continuously, checked the referenced categorical and coding definitions, and inspected the three rendered pages.

## Actual outline and mathematical functions

| Source lines | Function | Output |
| --- | --- | --- |
| 287–299 | Define the numerical recursion category from the fixed program interpretation | `Rec` and the description of its restriction idempotents |
| 301–330 | Apply the lifted-section theorem to the numerical diagonal pair | Numerical recursive inseparability of `A,B` |
| 332–358 | Define the total numerical carrier category and state Proposition 7.7 | Category comparisons, regularity/extensivity, syntax/list and proof initiality |
| 361–391 | Establish category comparisons and required categorical structure | Total-splitting and partial-map equivalences |
| 393–412 | Establish parameterized syntax/list initiality and identify substitution | Numerical realization of Appendix A's syntax structure |
| 414–427 | Establish derivation initiality | Initial inference algebra for a c.e. axiom subobject |
| 430–473 | Construct numerical sentence/proof objects and theorem ranges in the splitting | `S,ν,θ,c_T,t_T` |
| 475–488 | Apply the domain incompleteness theorem | Inseparability of theorem and refutation idempotents |

This is more than a proof of the numerical realization: it also proves numerical diagonal inseparability and applies the logical comparison to obtain numerical incompleteness. Those are separate substantive applications. The author's one-purpose requirement warrants a boundary between realization and incompleteness.

## Governing source

I consulted the supplied Knuth–Larrabee–Roberts *Mathematical Writing*, starting with §1, printed pp.1–5, and the definition-placement and audience discussions in §§4–5, printed pp.9–13. The applicable source principles are §1 point 5 (theorem statements), points 10–13 (connected explanations and reader expectations), point 14 (consistent notation), point 17 (unambiguous sentences), and point 26 (unnecessary jargon). The requirement that functors, algebras and morphisms have explicit types is the author's requirement and the plugin's supplementary convention; it is not a category-specific rule attributed to KLR.

## Necessary corrections

| Anchor | Actual difficulty | Principle or rationale | Recommended repair |
| --- | --- | --- | --- |
| pp.36–38, lines 301–330 and 475–488 | The subsection combines the realization theorem with two incompleteness applications. | Author's one-purpose requirement; KLR points12–13 concern the reader's path. | Keep the numerical category, Proposition7.7 and numerical logical-object construction under “The numerical realization.” Move the diagonal inseparability argument and the final incompleteness assembly into a separate subsection devoted to numerical incompleteness. Preserve their dependency on the fixed definitions from §7.1. |
| p.37, lines361–368 and 383–391 | The two equivalences are asserted through unnamed assignments, without object/morphism actions, comparison isomorphisms, or a named reverse assignment. The word “corresponding” suppresses the transport of a mono into the splitting. | Explicit-type requirement; KLR points11 and14. | Name the total comparison functor and give its carrier/arrow action; give a quasi-inverse using numerical tuple codes and state the comparison isomorphisms. Name the partial-map comparison, type its span assignment, and explain its inverse and compatibility with composition and restriction. |
| p.37, lines393–406 | The target `K_P`-algebra is only described as being “on” two arrows. Its structure morphism and the fold's algebra equation are not displayed. “The algebra operations are recursive on their specified carriers” should explicitly refer to partial recursive realizers rather than suggest global total extensions. | Explicit-type requirement; KLR points10–11 and14. | Declare the full algebra in `(C_rec/P)^2`, type both fold maps over `P`, and display their projection and algebra equations. Explain the finite evaluation algorithm using realizers of operations, with termination on the valid syntax carriers proved by induction and uniqueness proved in the same parameter fibers. |
| p.37, lines407–412 | “Evaluation of finite lists ... in the same way” suppresses the list algebra and fold. The numerical identification of free-variable and substitution operations is compressed into one unanchored “usual” assertion. | Explicit-type requirement; KLR points11 and17. | Type an arbitrary slice list algebra and its fold, state its nil/cons equations and uniqueness, and explicitly reuse the algorithms and defining equations proved in §5's substitution-realization proposition. State why uniqueness in the newly established numerical initial algebras identifies those algorithms with Appendix A's morphisms. Do not recopy Appendix A's categorical proof. |
| p.37, lines414–427 | The derivation initiality argument does not name the carrier conclusion map, its initial algebra structure, an arbitrary target algebra, or the fold's slice and algebra equations. | Explicit-type requirement; KLR points10–11 and14. | Declare the algebra in `C_rec/Fm`, the arbitrary target `((Q,q),α)`, and `h:(P_A,c_A)→(Q,q)`. Display `qh=c_A` and `hδ=αH_A(h)`, then justify computability, termination and uniqueness from the concrete tree traversal. |
| pp.37–38, lines393–395,449–457,475–477 | The numerical syntax is described as an unspecified encoding, but the application uses the exact diagonal formulas, substitution codes and standard interpretation from §7.1. Fixed-code compatibility should be stated before this identification. | Explicit presentation requirement; KLR point14. | Declare that the numerical realization uses the canonical syntax codes, parser and numerical constructor algorithms already fixed in §5, with the chosen recursive signature coefficients. Then the values of numerical `θ` agree with the fixed `Θ` and with the standard interpretation used in Lemma7.1. |
| p.37, lines442–457 and p.38, lines479–487 | The names `a,b` first appear only as “the partial identities ... on A,B”; their arrow types and passage through the inclusion should be explicit before the inequalities. The convention identifying c.e. subsets with split objects is stated, but the new `S,ν,θ` should be located in that convention without an implicit equivalence. | Explicit-type requirement and KLR point14. | Declare `a,b:ω⇀ω` in `Rec`, their partial-identity domains, and their total-splitting images. Give the split objects for the chosen sentence/proof carriers and the arrow types of `ν,θ,c_T,t_T` in the named splitting, or define them by a named comparison functor and state its object values. |

The finite-tuple comparison should include arity zero: a singleton carrier in `N^0` is encoded into `{0}⊆N`, rather than using a nonexistent bijection `N^0≅N`. For positive arities the fixed pairing gives recursive tuple codes and recursive decoding. This is a concrete detail of the comparison data requested in the second row, not a counterexample to the intended equivalence.

## Definition order and notation audit

The fixed object terms `O`, interpreted sets `|X|`, numerical bijections `γ_X`, graph formula `G`, index types `I(X,Y)` and universal index `u` are defined in §5. They are not missing definitions here. The opening should nevertheless state `X,Y∈O` when introducing `φ_e`.

Appendix A defines the finite-power convention, the two-sort syntax functor `K`, its parameterized version `K_P`, the option-valued substitution algebra, the inference endofunctor, and the image construction. These definitions may be imported by precise reference. Repeating their general proofs would be unnecessary and contrary to the appendix's role.

The present statement supplies a recursive signature but does not name the coefficient objects. An explicit statement should fix a nonnegative arity bound `d`, `V=N∈C_rec`, and recursive coefficient carriers `Σ_k,Π_k⊆N` for `0≤k≤d`. The corresponding constants in `K` then have declared categorical objects.

The category `C_rec` has the intended extensional morphism equality and operations computed by partial recursive programs total on the stated source carriers. The repair should preserve this distinction. An algebra operation is a total categorical arrow on a fiber-product carrier; its chosen numerical realizer can diverge outside that carrier. The fold argument should establish termination only on its declared syntax source.

The symbols `S,ν,θ` have earlier meanings in the syntactic total splitting. Their numerical versions can legitimately reuse notation after a declared change of ambient category, but the code comparison must be explicit. A categorical equivalence should not be used as literal equality of categories or objects.

The image of an arbitrary axiom mono can be used as an inclusion after the established computable inverse-on-image comparison; this is an isomorphism over the sentence object. The revised text should name that identification when changing tree labels from the axiom carrier to its image.

I found no invented technical term comparable to the earlier “coproduct table.” The issues are omitted categorical data and compressed comparisons. Existing terms such as “partial inverse,” “kernel pair,” “restriction monomorphism,” “parameterized initiality,” and “regular image” are appropriate.

## Recommended organization and exact data to display

Use the following dependency order:

1. **The numerical realization:** define `Rec` and `C_rec`, prove Proposition7.7 with explicit comparison functors and universal properties, and construct its sentence/proof objects and theorem images.
2. **Numerical incompleteness:** establish the numerical diagonal pair through Theorem3.5 and apply Corollary4.3 to the numerical theorem/refutation idempotents.
3. The existing numeral-instance and theory-extension subsection follows.

For the syntax fold, display data of this form, using the manuscript's chosen names:

```latex
Let $\alpha:K_P((X,\xi),(Y,\upsilon))
  \to((X,\xi),(Y,\upsilon))$
be an algebra in $(\mathcal C_{\mathrm{rec}}/P)^2$.
The fold has components
$h_T:(P\times\Tm,\pi_P)\to(X,\xi)$ and
$h_F:(P\times\Fm,\pi_P)\to(Y,\upsilon)$
in $\mathcal C_{\mathrm{rec}}/P$ and satisfies
$(h_T,h_F)\kappa_P=\alpha K_P(h_T,h_F)$.
```

For derivations, state the corresponding fully typed data:

```latex
Let $\delta:H_A(P_A,c_A)\to(P_A,c_A)$
be the constructor algebra in $\mathcal C_{\mathrm{rec}}/\Fm$.
For an algebra $\alpha:H_A(Q,q)\to(Q,q)$ in this slice,
the evaluation defines a unique slice morphism
$h:(P_A,c_A)\to(Q,q)$ with
$h\delta=\alpha H_A(h)$.
```

The proof must then establish the indicated equations and uniqueness using the numerical evaluation. These displays specify existing arguments; they do not supply the missing proof on their own.

For lists, an arbitrary structure has type
`β:1_P +_P ((P×V)×_P Z)→Z` in the slice on `z:Z→P`; the unique fold has type `(P×W,π_P)→(Z,z)` and satisfies the nil and cons equations. Naming the two operation restrictions is sufficient to write those equations without recopying the general list theory.

## Scope

Read completely: frozen §7.4 lines285–488. Inspected for dependency checks: §5's numerical types and graph coding, syntactic syntax/list and substitution realization; §6's interpretation carriers; §7.1's fixed diagonal formulas and maps; Appendix A's finite powers, syntax algebra, parameterized initiality, substitution, inference functor and theory-image construction. Consulted KLR §1 and §§4–5 as above. Rendered and visually inspected pages36–38; there is no clipping or unreadable layout in the current three pages.

This is a source-grounded editorial and explicit-type review of the named subsection. It does not establish falsity of the intended proposition, certify the whole manuscript, verify novelty or the bibliography, or constitute Lean elaboration. No manuscript edit, new literature claim or formalization has been performed by this reviewer.

**Closure condition:** the revised text must state and justify the comparison data and universal properties listed above, explicitly connect its numerical codes to the earlier fixed presentation, and give the subsection one mathematical purpose. Re-review the resulting snapshot rather than relying on this report as proof that the repairs were implemented.
