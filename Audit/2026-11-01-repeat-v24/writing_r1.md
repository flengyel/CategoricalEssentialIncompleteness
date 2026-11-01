# Mathematical Writing review — fresh review of version 24, §7.2

**Local result: PASS.** No necessary editorial or type correction was found in the reviewed snapshot. This judgment follows a fresh reading of the section, its relevant definitions, and the governing writing source; it does not rely on the earlier review reports. No manuscript edit is recommended merely to produce another version.

Manuscript: *Logical consequence and essential incompleteness in recursion categories*, version 24, §7.2, “An indexed family of arithmetic theories,” printed pages 31–35. Reviewed source: `tmp/review25/round1/08a-uniform-theories.tex`, SHA256 `bcf6666d968ac4a68e6351bf2c1497ee1d86724d8c33dfef26fecaf266f267bd`. The working manuscript section has the same hash. Line anchors below refer to this snapshot.

## Governing source and method

I consulted the supplied copy of Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*, starting with §1, printed pages 1–5, and the relevant discussions in §§4–5, printed pages 9–12. In particular, I checked the original contexts for §1 points 5, 10–17, 23–26 and the qualifications concerning the placement of definitions and audience in §§4–5. References below are to the source's printed page numbers. The categorical type requirements also come directly from the user's request and the plugin's supplementary conventions; they are not attributed to KLR as category-specific rules.

I read the entire 414-line section continuously, searched the modular manuscript for definitions before treating any notation as missing, and inspected the rendered pages 31–35 and the PDF text. I did not consult previous audit verdicts as evidence.

## Actual outline and mathematical function

The subsection has no further numbered subdivisions. Its existing order is:

| Source lines | Content | Function and dependency |
|---|---|---|
| 4–33 | Ambient category, inclusion, parameter object, interpretation, and axiom formulas | States the construction's purpose; defines one indexed presentation of all c.e. sentence axiom sets containing the chosen PA axioms. Uses the fixed syntax realization and arithmetic coding. |
| 35–63 | Predicate-category presentation and product isomorphism | Defines the numerical coordinates of the family axiom subobject. The explicit isomorphism prevents an arbitrary presentation from silently determining the meaning of the two numerical coordinates. |
| 65–124 | Parameterized rule objects, initial derivation algebra, sentence pullback, image, and range | Constructs the family in the total category, using the general initiality result of Lemma 5.8 and the image theorem of Appendix A.4. |
| 126–148 | Numeral morphisms and Proposition 7.5 | States that each standard numeral fiber recovers the corresponding derivation object and generated sentence theory. |
| 151–301 | Proof of Proposition 7.5 | Decomposes the parameter object into the numeral summand and its complement; defines the slice equivalence, decomposes the rule endofunctor, transfers the algebra category, proves initiality of the first component, and passes to sentence images. |
| 304–332 | Numerical presentation of the family conclusion map | Defines a single two-variable proof predicate and derives its PA-provable equivalence with each individually constructed proof predicate. |
| 335–413 | Theorem 7.6 and proof | Constructs a total morphism assigning an independent sentence to every consistent standard presentation, using functional search, the parameterized Turing property, and the preceding diagonal-domain lemma. |

The question answered is whether the separately realized arithmetic theories can be assembled into one internal family with the stated numeral fibers and a uniform total morphism selecting independent sentences. Proposition 7.5 gives the fiber comparison; Theorem 7.6 gives the uniform sentence morphism. The present order follows these dependencies. No revised outline is warranted.

## Comparison with Mathematical Writing

There are no necessary correction entries. The following table records the consequential checks and why the existing passages should be retained.

| Manuscript anchor | Check and result | Verified source principle or independent rationale | Action |
|---|---|---|---|
| p.31, lines 4–17 | The opening states what is being constructed before giving the ambient category and parameter object. It does not promote the result with unsupported adjectives. | KLR §1 points 12 and 24, printed pp.3,5: motivation and an effective opening. | Retain. |
| pp.31–32, lines 19–63 | The formulas, external sets of sentences, categorical axiom subobjects, and chosen numerical coordinates are distinguished. | KLR §1 points 11 and 14, printed pp.2–3; the user's explicit type requirement. | Retain the product isomorphism and graph definitions. |
| p.32, lines 65–124 | Displays are connected by prose explaining rule parameters, initiality, the sentence pullback, regular images, and range. The range paragraph supplies a mathematical identification rather than a reassurance. | KLR §1 points 10–13, printed pp.2–3: connected exposition, complementary explanation, and prose that remains intelligible when formulas are skimmed. | Retain. |
| p.33, Proposition 7.5 | Its parameter range, categorical conclusion, diagram, and consequent image statement are specified. The data referenced by the statement have already been fixed. | KLR §1 point 5, printed p.2, read together with §§4–5 on context and definition placement. Self-contained statements may refer to named, previously defined data. | Retain. |
| pp.33–34, lines 157–276 | The two slice functors, the natural comparison, and the induced algebra functor have declared categories and object/morphism actions. Naturality and full faithfulness are explained. | User's type requirement and supplementary categorical conventions; KLR §1 points 11,14,17. | Retain the explicit types and comparisons. |
| p.34, lines 278–301 | The argument distinguishes initial algebras from their underlying slice objects and derives the sentence image from the conclusion map. | KLR §1 points 11,14; independent requirement to distinguish levels of categorical structure. | Retain. |
| pp.34–35, lines 304–332 | Presentation choices, graph index, domain equivalence, and the uniform proof predicate are stated in an order that makes the numerical meaning checkable. | KLR §1 points 10–11 and 14. | Retain. |
| p.35, Theorem 7.6 and lines 344–413 | The theorem states totality through membership in the total category; consistency is imposed only in the quantified conclusion. The proof recalls the required maps and derives a typed diagonal identity before using it. | KLR §1 points 5,10–11,14; user's distinction between total maps, partial maps, and indices. | Retain. |
| Entire §7.2 | No empty promotional phrase, invented technical term, editorial-process statement, or defensive denial was found. Every paragraph defines data, states a result, explains a construction, or proves a mathematical inference. | KLR §1 point 26, printed p.5; plugin's manuscript-prose constraints. | No deletion warranted. |

The expressions “slice category,” “initial algebra,” “regular image,” “partial inverse,” “finite extensivity,” “natural isomorphism,” “full faithfulness,” and “essential surjectivity” have their established categorical meanings. “Inference endofunctor” is defined in Appendix A.4 and specifically imported here. “Derivation family” describes the displayed object over the parameter product; it does not introduce an additional undefined structure. “Standard” in “standard program index” distinguishes external natural-number indices from interpretations in nonstandard models, rather than substituting for a proof.

## Definition order and explicit type audit

The following are the important categories, constructions, and changes of level checked in reading order.

| Data | Explicit typing and definition status |
|---|---|
| `B`, `I`, `E`, `S`, `Fm`, `j`, `G_N` | Lines 6–17 declare the total splitting, inclusion functor and its object/morphism action, parameter object, syntax objects and sentence inclusion, and interpretation functor. The object and arrow actions of the interpretation are given in §6. |
| `W`, `Ax`, `Gamma_e`, `A_{Gamma_e}` | Lines 19–33 distinguish arithmetic formulas, external sets of sentences, and subobjects. The arithmetic language has the single sort of PA, declared in §5. The external parameter is explicitly `e in N`. |
| `J`, `Top`, `D`, `A_0`, `r_0`, `r_1`, `v`, `a`, `i` | Lines 35–63 specify the predicate-category equivalence, formula objects, represented arrows and their graphs, product isomorphism, predicate inclusion, and final monomorphism in `B`. The equivalence is not treated as a literal equality of categories. |
| `L`, `R_n`, `lambda`, `p_n`, `q_n`, `F_E`, `R_n^E` | Lines 65–80 state their ambient category, arity ranges, endpoints, and nullary data. The original rules come from Appendix A.5. |
| `u_n`, `v_n`, `pi_{n,k}`, `d_n`, `p_n^E`, `q_n^E` | Lines 82–93 declare endpoints and the component index range. Finite powers and their action on arrows, including arities 0 and 1, are defined in Appendix A.1; no exponential is being assumed. |
| `H_E` | Lines 95–99 declare its source and target slice. Appendix A.4 specifies the general object/morphism action, and the current section supplies every rule object and arrow needed to instantiate it. Repeating the general construction here would duplicate the appendix. |
| `mathfrak P`, `(P^all,c^all)`, `alpha` | Lines 100–109 distinguish an algebra, its slice object, and its structure arrow. Lemma 5.8 applies to arbitrary finite-arity rule morphisms in `B_PA`, not just an individual axiom subobject. |
| `c`, `m`, `r`, `t` | Lines 110–123 give the total conclusion map, regular-image monomorphism, partial inverse in the splitting category, and partial range idempotent. The switch from `B` to `Split(S_PA)` is explicit. |
| `epsilon_e`, `!_X`, `k_e^X` | Lines 126–130 give their endpoints and object/parameter ranges. The numeral map is a total arrow in the ambient total category. |
| `P_{Gamma_e}`, `c_{Gamma_e}` | Introduced in §7.1 as the sentence pullback of the full derivation object. The diagram in Proposition 7.5 types their specialized use. This is not missing notation. |
| `E_{ne e}`, `u_e`, `k_{ne e}^X` | Lines 151–156 specify the complementary split object, inclusion and product inclusion. The copairing has the stated codomain and is declared an isomorphism. |
| `Xi_e`, `Psi_e` | Lines 157–191 specify both functor signatures, object actions, arrow actions, and the equivalence supplied by finite extensivity. The two components of `Xi_e(f)` have their slice endpoints. |
| `F_{ne e}`, `pi_E`, `rho_n`, `R_n^{ne e}`, `s_n`, `t_n`, `p_n^{ne e}`, `q_n^{ne e}` | Lines 193–215 give the complement rule data, all endpoints, arity range, and the equations characterizing the premise and conclusion maps. The nullary case uses the declared finite-power convention. |
| `H_e`, `H_{ne e}`, `zeta` | Lines 213–250 declare the endofunctors, natural transformation, component endpoints and component categories. The naturality equation has a stated common source and target. |
| `Lambda_e` | Lines 252–276 declare the algebra categories, structure-map action and underlying slice-arrow action. Algebra morphisms and underlying arrows are explicitly distinguished. The composition with `zeta^{-1}` has the correct direction. |
| `mathfrak P_e`, `mathfrak P_{ne e}`, `mathfrak Q` | Lines 278–295 treat these as algebras and state the category of the final algebra isomorphism. The underlying pullback slice object is stated separately. The proof using the second component's identity establishes uniqueness in the first component. |
| `P_0`, `u`, `gamma_c`, `a_c`, `Prov` | Lines 304–332 distinguish a formula object, an isomorphism in `B`, a morphism in the predicate category, a natural-number program index, its graph formula, and the two-variable provability formula. The type of `v^{-1}cu` is displayed. |
| `q`, `theta`, `Theta`, `Neg`, `C`, `C'`, `R` | Theorem 7.6 and lines 344–356 distinguish the total categorical arrow, the numerical functions from §7.1, and arithmetic formulas. §7.1 explicitly declares graph-definition shorthand for the numerical functions used inside formulas. |
| `a_ell`, `ell`, `tau_PA`, `b`, `h`, `g`, `I(g)` | Lines 358–393 distinguish typed program indices, partial arrows, the total parameter map, and its image in the splitting category. Both sides of the partial diagonal identity have the same displayed source and target. |
| `e`, `n`, `K`, `F_N(ell)`, `D_0`, `D_1` | Lines 395–413 state the external parameter, external numerical value, first-order model, interpreted partial-function type, and numerical domain memberships. The sets `D_i` and the functor `F_N` have prior definitions in §§7.1 and 6. The final equality is between numerical codes. |

Local reuse of letters inside proposition proofs is unambiguous. In particular, the local structure map `q` in a slice object `(Q,q)` is bound inside Proposition 7.5's proof; the total arrow `q:E->S` is introduced independently in Theorem 7.6. There is no reason to add a collection of new subscripts solely to prevent this conventional scoped reuse.

The construction is categorical, but the entire application section is not formulated solely in an internal categorical language. The derivation family, its fibers, and its images are objects and arrows in `B`, its slices, and the stated algebra categories. The numerical presentations pass through the explicitly named equivalence `J`, the product isomorphism `v`, and the presentation isomorphism `u`. The assertion that the family covers all c.e. presentations quantifies externally over `e in N` and the sets of sentences `Gamma_e` (lines 27–33). Theorem 7.6 evaluates the constructed arrow using `G_N`, and its proof explicitly invokes `F_N` and a first-order model `K` (lines 335–413). These uses of the metatheory are declared and occur where the categorical construction is applied. No unmarked identification of an internal object with a set, or of a formula with its numerical code, was found. This conclusion should not be overstated as saying that §7.2 contains no set-theoretic or model-theoretic reasoning.

## Prioritized edits and replacement wording

No necessary edit or exact replacement is proposed. The fully typed data, categorical comparisons, and numerical presentations are mathematically functional. Shortening these passages to generic words such as “transport,” “naturality,” or “the usual construction” would remove explanations that the user has required.

The appendix remains used by reference for the general rule endofunctor and the least-image theorem. The section proves its new fiber argument and numerical application rather than repeating the appendix's proofs. No change to Appendix A is indicated by this editorial review.

## Scope and limits

This is a source-grounded editorial and type review of §7.2, not a whole-paper review or a certification of correctness or novelty. I checked relevant passages in §§5–7 and Appendix A to resolve dependencies and definitions. I did not reprove every imported theorem, reverify every bibliography entry, or perform a new literature search; no new literature claim is proposed. I inspected the five rendered pages and found no clipping, unresolved reference, or illegible display in this section. I did not compile a new version because this review makes no source change.

**Acceptance endpoint for this review:** no unresolved necessary editorial or explicit-type finding in the named snapshot. **Result: met.**
