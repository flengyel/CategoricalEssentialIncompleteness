# Detailed outline of the paper, version 37

Florian Lengyel, *Logical consequence and essential incompleteness in recursion categories*, 1 November 2026. Reviewed commit: `47be761bc05fa0d176b2f9a48f5f63db63b9fa79`. The manuscript remains version 37.

This outline records the existing section order, each subsection's function, its main results, and its dependencies. Two agents read all fourteen main-section sources and all four appendices completely; the separate construction and writing assessments checked the central argument chains. There are 62 theorem, proposition, lemma, or corollary environments and three numbered definitions. This is an outline and explanation audit, not a new certification of every proof or bibliography item. Result numbers and starting-page locators were checked against the compiled version 37 labels.

## 1. Central construction and argument


The paper constructs categorical syntax and inference, then obtains the provable sentences of a chosen axiom subobject as the image of the derivation-conclusion morphism. Negation supplies the refutable sentences. Its incompleteness arguments concern these two domains of sentences. The essential-incompleteness conclusions require either applying the semantic comparison to every effective consistent extension, or retaining a fixed reduction from an inseparable pair as the axiom subobject grows.

The constructions use three levels that the abstract presently compresses:

| Level | Mathematical data and purpose |
| --- | --- |
| Recursion category `R` | Partial morphisms, restrictions and ranges, and a Turing morphism provide the recursion-theoretic argument and its inseparable pair. |
| Restriction splitting `Split(R)` | Restriction idempotents acquire splitting objects. A sentence carrier or derivation carrier can therefore be an object even when it is only a restriction domain on an original object of `R`. |
| Total category `D = Tot(Split(R))` | Syntax constructors, inference rules, derivations, axiom inclusions, and conclusion morphisms are total morphisms here. Regularity and the specified initial algebras are hypotheses in the general account and are proved in the realizations. |

For an axiom subobject `A ↪ S` in `D`, with `S ↪ Φ` the sentence subobject of the formula object, the inference endofunctor has an initial algebra with conclusion morphism `c_A:P_A→Φ`. Pulling back to sentences gives `c_{A,S}:P_{A,S}→S`. Its regular image `T_{A,S}↪S` is the least sentence theory containing `A`: it is the subobject of sentences obtainable by the internal inference rules from those axioms. Where the image inclusion has the specified partial inverse, its partial identity is

\[
t_A=\operatorname{ran}(c_{A,S}):S\rightharpoonup S
\quad\text{in }\operatorname{Split}(\mathscr R).
\]

Thus “generated theory” is not a second construction unrelated to the internal deductive system. It is its deductive closure, obtained by retaining the conclusions of derivations. The inverse image `ν* t_A` along sentence negation represents refutable sentences. In the syntactic realization, Theorem 5.9 also gives an original `S_T` restriction idempotent on `ω` representing this theory; its splitting is the theory object in the total category.

The phrase “regular categories of total morphisms in the restriction splittings” names the ambient construction but does not, on its own, explain this logical role. The role of regularity is to take the image of the conclusion morphism; the role of splitting is to provide the objects represented by the restriction domains. These roles, rather than an unexplained list of categorical properties, are what connects the setup with the rest of the paper.

## 2. Main sections


### 1. Introduction; 1.1 Related work

**Function:** previews the comparison criterion and examples, then locates them among recursion-category existence theorems, partial-map frameworks, and earlier inseparability results.

The actual opening starts with Corollary 3.3 and lifted complementary conditionals. It then describes the Miller category and cut pair, its expanded field theory, syntactic categories and their faithful all-model interpretation, the numerical application, and the cosheaf application. The explicit Di Paola–Heller motivation occurs in Related work. This is the current organization, not the logical order of the constructions below. In particular, the all-model interpretation described here is auxiliary to the fixed-category arithmetic proof used in Section 7.

**Anchor:** `sections/01-introduction.tex`.

### 2. Categorical preliminaries (pp. 3–5)

**2.1 Partial maps and restriction idempotents.** Defines restriction categories, total morphisms, restriction functors/equivalences, the restriction order, compatible joins, restriction zeros, complementary and inseparable domains, inverse image, ranges with their agreement law, restriction splitting, and the Karoubi envelope. This supplies the meanings of the domains and categorical completions used later.

**2.2 Products, coproducts, and local connectedness.** Defines restriction products and coproducts, range functors and their canonical coproduct comparison, connected domains, local connectedness, sections, partial monomorphisms, and weak choice. The product-doubling example shows that a range functor need not preserve restriction products. Local connectedness is background and a property of examples; it is not a hypothesis of the central comparison theorem.

**2.3 Recursion categories.** Defines prodominical and isotypical categories, Turing morphisms and their total parameter maps, recursion categories, restriction terminal objects, and Turing categories. This separates the terminal-free isotypical recursion setting from the cartesian Turing setting available after the appropriate completion.

**Anchor:** `sections/02-categorical-preliminaries.tex`; no numbered result in this section.

### 3. Diagonal comparison and complementary conditionals (pp. 5–7)

**3.1 The comparison theorem.** Theorem **3.1**, `thm:comparison`, starts with a range functor `F:R→A`, a source Turing morphism `τ`, and an isomorphism `b:U→U+U`. From `h=bτΔ_U` it obtains two disjoint source domains `a_0,a_1`. Let disjoint target domains `P,N` contain their images. If the reversed partial conditional for `P,N` lifts through `F`, the Turing property produces a total source morphism whose interpretation has zero inverse image of both target domains. Nonzero interpreted identity and preservation of the relevant join exclude `P∨N=1`. Corollary **3.2**, `cor:separator`, excludes such a lift for a complementary target separator.

**Dependency and contribution:** depends on the restriction/range and coproduct calculus of Section 2 and the source Turing property. It is a comparison of restriction domains, not yet a theorem about logical theories. It does not assume product preservation by `F` or local connectedness of the source.

**3.2 Complementary conditionals.** Corollary **3.3**, `cor:source-conditionals`, obtains source inseparability when every complementary source pair has a total morphism choosing opposite coproduct injections. Proposition **3.4**, `prop:disjoint-joins`, constructs these morphisms as joins of the two branch morphisms when joins of disjoint parallel morphisms exist.

**Dependency and contribution:** reduces inseparability to a concrete source construction. Appendix C shows that the lifting requirement cannot be inferred merely from faithfulness and product/range preservation.

**Anchor:** `sections/03-sections-and-inseparability.tex`.

### 4. Internal theories and semantic consistency (pp. 7–10)

**4.1 Theories and their interpretation.** Sets up `D=Tot(Split(R))` with the categorical syntax and initial inference algebras of Appendix A. The regular image of the sentence-conclusion morphism is the generated sentence theory; a partial inverse identifies its partial identity with a range. Theorem and refutation domains are `t_A` and `ν*t_A`. A range functor extends through chosen restriction splittings and preserves the represented theories. Proposition **4.1**, `prop:interpreted-theory`, proves that a soundness factorization through a validity subobject places the interpreted theorem subobject inside that validity subobject. If validity is disjoint from its inverse image under negation, the interpreted theorem and refutation domains are disjoint.

**4.2 Incompleteness from semantic consistency.** Theorem **4.2**, `thm:logical-comparison`, applies Theorem 3.1 to the interpreted theorem/refutation domains pulled back along a total sentence morphism `θ:U→S`. Its additional data are the two reduction inequalities and the specified partial conditional lift. It proves incompleteness of both the interpreted theory and the source theory, and supplies a total family avoiding both interpreted domains.

**4.3 Inseparability in the source.** Corollary **4.3**, `cor:domain-incompleteness`, is a separate extension criterion. A total morphism reducing a fixed source-inseparable pair into a base theory/refutation pair continues to do so for any larger theory. If that larger theory is consistent, its theorem/refutation domains remain inseparable, hence do not cover the sentence object. The source pair retains inseparability under the full inclusion into the restriction splitting.

**Dependency and contribution:** Appendix A supplies the logical construction. Section 3 supplies the computational comparison. This section connects them. Proposition 4.1 alone establishes interpreted consistency, not essential incompleteness; Theorem 4.2 and Corollary 4.3 have distinct extra hypotheses. The arithmetic semantic argument uses Theorem 4.2; numerical, Miller, and cosheaf arguments use Corollary 4.3.

**Anchor:** `sections/03a-internal-theories.tex`.

### 5. The syntactic recursion category (pp. 10–23)

**Section opening.** Constructs `S_T` for a consistent extension `T⊇PA`, using closed object terms and program indices modulo universal `T`-provable graph equivalence. Lemma **5.1**, `lem:arithmetized-evaluation`, supplies formalized evaluation, specialization, and composition. These give a well-defined category, restrictions/ranges, products/coproducts, and a Turing morphism. The term presentation is equivalent to the unprimed set presentation. The primed pointwise relations are distinguished because their proposed composition is not well-defined.

**5.1 The total restriction splitting.** Lemma **5.2**, `lem:syntactic-functional-search`, represents a functional Σ₁ relation by witness search. Lemma **5.3**, `lem:syntactic-total-category`, identifies `B_T=Tot(Split(S_T))` with a predicate category whose morphisms are `T`-provably total functional Σ₁ graphs. It proves regularity, disjoint pullback-stable finite coproducts, partial inverses of monomorphisms, and the expected image formula. The partial-map equivalence and Turing-category structure of `Split(S_T)` follow.

**5.2 Syntax and lists.** Lemma **5.4**, `lem:st-finite-sigma1`, combines finitely many Σ₁ membership conditions. Propositions **5.5–5.6**, `prop:st-syntax-initiality` and `prop:st-list-initiality`, prove the syntax and list initial-algebra properties, stable in every parameter slice. The signatures have a fixed finite arity bound, with coefficient objects in `B_T`; numerical presentations do not replace the universal-property proofs.

**5.3 Free variables and substitution.** Proposition **5.7**, `prop:st-substitution-realization`, verifies the algorithms for lists, free variables, term substitution, and option-valued formula substitution against the appendix folds. The admissibility subobject is complemented and is the free-for substitution domain on the named-variable syntax.

**5.4 Derivations and theories.** Lemma **5.8**, `lem:syntactic-derivation-initiality`, constructs the initial inference algebra for arbitrary fixed finite rule data in `B_T`. Theorem **5.9**, `thm:syntactic-generated-theory`, realizes Appendix A's first-order syntax and deduction. For every axiom subobject, the conclusion image is its least deductively closed formula subobject, and its sentence part is the least sentence theory. A displayed restriction idempotent `t_A` in original `S_T` represents the sentence theorem predicate; its splitting represents the generated theory.

**Dependency and contribution:** proves that the abstract logical construction really exists in the syntactic recursion setting, including its quantifiers, substitution, derivations, and leastness. It supplies the sentence/theorem objects used in Sections 6–7. This is not yet a soundness or incompleteness proof.

**Anchors:** `sections/05-syntactic-recursion-category.tex`; `sections/05a-internal-syntax.tex`.

### 6. Interpretation and soundness (pp. 23–28)

**Section opening.** Proposition **6.1**, `prop:model`, interprets `S_T` in partial functions for each model `M⊨T`, preserving the stated restriction/range/product/coproduct structure. Arithmetic quantifiers in the interpretation range over the entire model, including nonstandard elements.

**6.1 Lifting complementary conditionals.** Lemma **6.2**, `lem:switch`, constructs total source conditionals from complementary `T`-provable predicates. Corollary **6.3**, `cor:model-pair`, applies Corollary 3.3 using one model to prove inseparability of the syntactic diagonal pair.

**6.2 The total interpretation functor.** Proposition **6.4**, `prop:model-total-regular`, proves that `G_M:B_T→Set` preserves finite limits, finite coproducts, and regular images. This lets the represented theory image be interpreted as the actual image of the interpreted conclusion function.

**6.3 Soundness on standard codes.** Lemma **6.5**, `lem:semantic-substitution`, proves semantic substitution for the realized free-for condition. Proposition **6.6**, `prop:standard-code-soundness`, takes a c.e. axiom set `Γ` represented in the fixed `B_PA` and a structure `K⊨Γ`. Standard arithmetic interprets syntax/derivation codes; `K` interprets the decoded formulas. Induction on finite derivations gives a factorization of the sentence-conclusion function through the codes of sentences true in `K`. This validity subset and its negated inverse image are disjoint.

**6.4 Ultrapowers of the code interpretation.** Lemma **6.7**, `lem:ultrapower-regular`, proves the set-ultrapower functor preserves the required finite structure and images. Lemma **6.8**, `lem:ultrapower-comparison`, gives a natural isomorphism between the ultrapower of `G_N` and interpretation in the arithmetic ultrapower. Theorem **6.9**, `thm:ultrapower-soundness`, transports the factorization and disjointness, including nonstandard code elements.

**Dependency and contribution:** interprets the internally constructed derivations without assuming that the represented axiom theory holds in standard arithmetic. The separate roles of `N` and `K` are essential. This is soundness for the constructed standard interpretation and its arithmetic ultrapowers, not a claim of soundness for arbitrary arithmetic-model interpretations of arbitrary represented axiom sets.

**Anchor:** `sections/06-interpretation-in-models.tex`.

### 7. Essential incompleteness of arithmetic (pp. 28–43)

**7.1 Comparison in the fixed syntactic category.** Keeps the ambient recursion category fixed at `S_PA` while represented c.e. arithmetic axioms `Γ` vary. Lemma **7.1**, `lem:arithmetic-diagonal-representation`, constructs numeral substitution and the interpreted reduction inequalities when `Γ` derives PA. Lemma **7.2**, `lem:arithmetic-proof-search`, gives the partial proof-search conditional and its source lift. Theorem **7.3**, `thm:arithmetic-internal-comparison`, uses a model of each consistent `Γ`, Section 6 soundness, and Theorem 4.2 to obtain incompleteness internally and under standard/ultrapower interpretation; it also supplies a total family of independent standard sentences. Corollary **7.4**, `cor:arithmetic`, proves recursive inseparability of theorem and refutation sets for every consistent c.e. PA extension, hence essential incompleteness.

**7.2 An indexed family of arithmetic theories.** Constructs one axiom subobject over an enumeration-index object `E`, one initial derivation algebra, and one theorem subobject of `E×S`. Proposition **7.5**, `prop:arithmetic-theory-fibers`, identifies the numeral fibers with the derivation algebras and generated theories of the individual `Γ_e`.

**7.3 Uniform independent sentences.** Theorem **7.6**, `thm:uniform-independent-sentences`, constructs one total morphism `q:E→S` in `B_PA`; for each standard index `e` whose `Γ_e` is consistent, its interpreted value codes a sentence neither provable nor refutable from `Γ_e`. It uses the indexed theory, parameterized Turing property, proof-search lift, and standard soundness.

**7.4 The numerical realization.** Proposition **7.7**, `prop:numerical-structure`, identifies `Tot(Split(Rec))` with the regular category `C_rec` of c.e. numerical carriers and computable functions total on them, and identifies the respective partial-map categories. Proposition **7.8**, `prop:arithmetic-theory-realization`, realizes the same first-order syntax/list/derivation universal properties there. Explicit computable relabelings compare the numerical proof and theorem carriers with the standard interpretation of the syntactic realization.

**7.5 Numerical incompleteness.** Applies Corollary 3.3 in ordinary partial recursion to obtain one recursively inseparable pair. Its numeral-substitution reduction into the PA theorem/refutation domains persists under every consistent c.e. extension, so Corollary 4.3 gives the numerical incompleteness conclusion.

**7.6 Numeral instances and theory extension.** Packages the increasing theorem/refutation numeral-instance pairs as a covariant functor under theory inclusion. It compares this reduction argument with Bernardi's use of precomplete equivalence relations.

**Dependency and contribution:** Section 7 gives both the fixed-syntactic semantic-comparison application and a numerical source-inseparability realization. The numerical category also supplies the total base used to build the cosheaf example in Section 9.

**Anchors:** `sections/08-essential-incompleteness-of-arithmetic.tex` and its four included `08a`–`08d` sources.

### 8. Miller sequences and essential incompleteness (pp. 43–49)

**Section opening.** Fixes a Miller sequence with the required index property and its nonempty compact space of binary representations.

**8.1 Computation independent of the binary representation.** Lemma **8.1**, `lem:miller-unanimity`, uses compactness to compute unanimous halting with one program from any representation. Proposition **8.2**, `prop:miller-category`, constructs `E_a`: one program must compute the same partial function, including its domain, from every binary representation. It proves the recursion structure, ranges, compatible joins, local connectedness, weak choice, and Turing property. Source conditionals and Corollary 3.3 give its diagonal inseparable pair. Fixed-representation inclusions are faithful range functors.

**8.2 The index sets below and above 1/2.** Lemma **8.3**, `lem:miller-cut-reduction`, gives an ordinary total recursive reduction of the diagonal pair to `L_a={n:a(n)<1/2}` and `R_a={n:a(n)>1/2}`. Corollary **8.4**, `cor:miller-cuts-inseparable`, proves their inseparability in `E_a`, despite the existence of a separator computed from each fixed representation. Thus a faithful product-preserving range functor can send this inseparable pair to a separable pair; it does not preserve the chosen Turing morphism's universality.

**8.3 A theory of real closed fields.** Proposition **8.5**, `prop:miller-theory-realization`, proves the regularity, partial inverses, syntax/list initiality, and initial derivations needed for Appendix A in `D_a=Tot(Split(E_a))`. The axiom theory expands real closed ordered fields by constants and the strict rational bounds specified by the sequence; the real field interprets it consistently. Theorem **8.6**, `thm:miller-incompleteness`, reduces the inseparable cut pair to its theorem/refutation domains. Corollary 4.3 gives incompleteness for every consistent extension whose axiom set is semidecidable by one oracle program from every binary representation, with the same membership outcome.

**Dependency and contribution:** an application beyond ordinary numerical recursion whose effective extension class is representation-independent. The logical system is first-order logic with equality; the incompleteness claim concerns the expanded field theory, not real closed fields in their usual complete language. The extension condition must retain its single-program uniformity.

**Anchor:** `sections/04-miller-sequences.tex`.

### 9. A recursion category from a three-point space (pp. 49–56)

**Section opening.** Describes the three-point space and its equivalence between set-valued cosheaves and covariant functors on `J=(1←0→2)`. The computable total category is `E=C_rec^J`; its partial-map category is `A=Par(E,Mono)`. Appendix B supplies a universal object, frame, and Turing morphism, producing a recursion subcategory `R_X` with `Split(R_X)≃A` and `Kar(R_X)≃A`. Formula and derivation objects are constructed in `E=Tot(A)`.

**9.1 Complementary domains and inseparability.** Builds source conditionals by decomposing complementary c.e. subfunctors. Corollary 3.3 then yields inseparability in `R_X`. A terminal-subobject invariant distinguishes this recursion category from ordinary partial recursion.

**9.2 Evaluation functors.** Proposition **9.1**, `prop:endpoint`, proves component evaluations preserve restrictions, ranges, zeros, products/coproducts, and joins. The two endpoint evaluations preserve the constructed Turing morphism; the middle evaluation does not. Probe descriptions relate these categorical domains to ordinary c.e. component subsets.

**9.3 Propositional theories and component theorem sets.** Transports the diagonal pair to two disjoint c.e. subfunctors of atoms, independently recursively inseparable at each endpoint. Proposition **9.2**, `prop:fork-syntax-initial`, constructs the internal propositional formula algebra with atom, negation, and implication constructors. Proposition **9.3**, `prop:fork-proof-initial`, constructs the initial algebra of derivations from the logical schemes and positive/negative atomic axioms under modus ponens. Theorem **9.4**, `thm:fork-proof-presentation`, identifies the conclusion image as the least deductively closed c.e. subfunctor and proves consistency. Theorem **9.5**, `thm:cosheaf-observation`, uses Corollary 4.3 for compatible consistent c.e. extension families, obtaining categorical inseparability and endpoint recursive inseparability/incompleteness. Corollary **9.6**, `cor:cosheaf-essential-incompleteness`, obtains essential incompleteness of each of the two endpoint theories for every consistent c.e. axiom extension in its own language.

**Dependency and contribution:** a propositional realization in a recursion category not restriction-equivalent to ordinary numerical recursion. The theorem image is simultaneously an internal theory subfunctor and a family of ordinary component theories. Endpoint evaluation supplies the concrete essential-incompleteness conclusions.

**Anchor:** `sections/09-three-point-space.tex`.

## 3. Appendices

### A. Syntax and deductively closed theories


Appendix A, **Syntax and deductively closed theories**, begins on p. 56 (A.1 begins on p. 57) and has one function: specify the categorical deductive systems and construct the theories generated by their axioms. Its general construction precedes the numerical and other realization proofs in the applications.

| Existing subsection | Mathematical function, results, and dependencies |
| --- | --- |
| **A.1 Categorical hypotheses and notation** (p. 57) | Fixes a regular category `D` with finite coproducts. Disjoint pullback-stable coproducts are added for first-order syntax; those extra coproduct conditions are not needed for the general closure theorem A.5. Specifies Boolean tests and conditionals categorically, finite products with chosen associations, a variable object `V∈D` with decidable equality, coefficient objects for bounded-arity function/relation symbols, and stability of initial algebras under parameters. Its role is to make the later constructor, side-condition, and substitution morphisms available. |
| **A.2 Terms, formulas, and free variables** (p. 58) | Defines a two-sorted endofunctor `K:D²→D²`. Definition **A.1** specifies raw named-variable syntax `(Tm,Fm)` as a parameter-stable initial `K`-algebra, together with a parameter-stable list object `LV`. The constructors include equality, relation symbols, negation, implication, and universal quantification. Folds define lists of free-variable occurrences. Definition **A.2** defines the sentence subobject `S→Fm` by the empty-free-variable pullback. Negation restricts to `S`; existential quantification is derived. |
| **A.3 Admissible substitution** (p. 60) | With parameter object `E=V×Tm`, constructs term substitution `a_T:Tm×E→Tm` and option-valued formula substitution `b_F:Fm×E→1+Fm`. Proposition **A.3** obtains the complemented admissibility subobject and successful substitution by pullback. The quantifier clause distinguishes a bound substituted variable, tests variable capture, and retains the original body where required. Parameterized induction proves identity substitution and substitution at absent variables. This supplies the side conditions and morphisms for the first-order axiom schemes. |
| **A.4 Inference rules and deductively closed subobjects** (p. 61) | Given a formula object `F`, rule-instance objects `R_n` and morphisms `p_n:R_n→F^n`, `q_n:R_n→F` define an inference endofunctor `H:D/F→D/F` using pullbacks and finite coproducts. Nullary rules are axioms. Definition **A.4** identifies a closed formula subobject with an `H`-algebra whose underlying map to `F` is monic. Theorem **A.5**, p. 62, proves that the regular image of the conclusion morphism of an initial derivation algebra is the least rule-closed subobject. The proof uses regularity and preservation of regular epimorphisms by `H`. This is the central abstract construction. |
| **A.5 First-order theories** (p. 63) | Builds the logical-axiom object from three propositional schemes, quantifier instantiation and distribution, and equality reflexivity and substitutivity. The admissibility and free-variable subobjects supply the quantifier/equality side conditions. Given sentence axioms `A→S`, axiom introduction, generalization, and modus ponens define `H_A`. Theorem **A.6** applies A.5: `im(c_A)→Fm` is the least closed formula subobject, and its sentence pullback is `T_{A,S}→S`. The following paragraphs establish least sentence-theory closure and monotonicity under axiom inclusion. Lemma **A.7**, p. 64, relates a regular image to a restriction range when its monic inclusion has a partial inverse. This makes generated theories available to the restriction-domain comparison of Section 4. |
| **A.6 Propositional theories** (p. 65) | Replaces first-order syntax by the initial algebra of `Z↦V+Z+Z²`, with atom, negation, and implication constructors. Uses the three propositional axiom schemes and modus ponens, and applies A.5 to obtain the least closed sentence subobject. Positive and negative atom subobjects specify nonlogical axioms. This is the construction used in Section 9. It does not require the variable-equality/substitution machinery used for first-order logic. |

The dependency order is substantive: Boolean decisions and parameterized recursion support substitution; substitution supports the first-order schemes; the inference endofunctor and initial derivation algebra support the image theorem; the image–range identification supports the incompleteness application. Removing the technical setting from the abstract does not remove any of these dependencies from the appendix.

### B. The three-point cosheaf construction


Appendix B, **The three-point cosheaf construction**, begins on p. 65 and proves the computational and categorical infrastructure used by Section 9. The logical theory construction itself is in A.6 and Section 9.3.

| Existing subsection | Results and function |
| --- | --- |
| **B.1 Cosheaves and functor categories** | **B.1** identifies set-valued cosheaves on the chosen three-point space with `Set^J`; the whole-space value is a pushout. Examples distinguish categorical products and subobjects from setwise products and inclusions at the whole open space. **B.2** proves `E=C_rec^J` regular and extensive, with componentwise monomorphisms and regular images, using Proposition 7.7. |
| **B.2 Partial maps, ranges, and connected restriction idempotents** | **B.3** proves `A=Par(E,Mono)` split, prodominical, with restriction products/coproducts, weak choice, ranges, and the required inverse-image laws. Its ranges are partial identities on regular images. **B.4** proves local connectedness by connected finite subfunctors detecting component values and definedness. |
| **B.3 A universal object and a frame** | **B.5** embeds every object of `E` into the designated object `V` by a restriction monomorphism. Constructs nonempty-word formation. **B.6** proves `V≅V×V`, `V≅V+V`, and `V≅V#`. These are inputs for the recursion-category construction. |
| **B.4 A Turing morphism** | **B.7** constructs `τ:V×V⇀V` as a partial natural transformation and proves its parameterization property for every object of `A`. Endpoint components are ordinary numerical Turing morphisms; the central component includes the naturality compatibility tests. |
| **B.5 The recursion category and its splitting** | **B.8** constructs the isotypical full recursion subcategory `R_X`, proves its inclusion is a range functor, and establishes `Split(R_X)≃A`. **B.9** also gives `Kar(R_X)≃A`. **B.10** distinguishes `R_X` from ordinary partial recursion using terminal-object subobjects, and proves the atom object `V` has no decidable equality in `E`. Section 9 uses this `V` as its propositional atom object. The no-decidable-equality assertion concerns this `V`; it is not a general impossibility theorem for first-order realizations using other objects of `E`. |

### C. Necessity of section lifting for inseparability


Appendix C, **Necessity of section lifting for inseparability**, begins on p. 72 and contains **Proposition C.1**. It constructs a recursion category `C_K` of partial numerical functions with `K`-c.e. domains and ordinary partial recursive extensions. The inclusion into partial functions is faithful, preserves the listed range/restriction/product/coproduct structure, reflects zero, and has nonzero identity image. Nevertheless its chosen diagonal pair is separable. A target characteristic section has no source lift; disjoint source morphisms need not have a common upper bound.

Its role is to establish the substantive necessity of the comparison's lifting premise. It is not another construction of logical theories and need not be described in an abstract focused on the main logical contribution.

### D. Faithful families and theory extension


Appendix D, **Faithful families and theory extension**, begins on p. 74 and gives an auxiliary representation of the syntactic categories.

| Existing unit | Results and function |
| --- | --- |
| **Section opening** | **D.1** combines interpretation in all arithmetic models on a countable carrier into a faithful range functor `F_T:S_T→∏_M Pfn`. Proves the target split and locally connected with weak choice and suitable inverse-image laws. Gives the strictly commuting square for ambient theory extension `T⊆T'`. |
| **D.1 Inseparable pairs under theory extension** | **D.2** derives a source inseparable pair and its persistence under the quotient functors `S_T→S_T'`. Explains that the image of the Turing morphism is not universal in the all-model product and arbitrary target separators need not lift. |
| **D.2 Numeral observations** | For a restriction domain represented by `C`, the c.e. numerical set of standard `n` with `T⊢C(n)` is expressed by composition with constant morphisms, and equivalently by the faithful interpretation. |
| **D.3 A complete ambient theory** | Identifies `S_Th(N)` with ordinary partial recursion. Its ambient theory is complete although the category has inseparable pairs. This separates computational inseparability in a category from incompleteness of an arbitrarily chosen ambient theory. The internally represented logical theory and its reduction/consistency data are necessary for the latter conclusion. |

Appendix D is not the soundness argument for arbitrary nonstandard syntax codes. The main arithmetic argument uses standard syntax interpretation and its arithmetic ultrapowers, not the faithful all-model family.

## 4. Principal instances and auxiliary material


| Role | Recursion category / total setting | Internal deduction and incompleteness result |
| --- | --- | --- |
| Syntactic instance | `S_T`; deduction in `B_T=Tot(Split(S_T))`, with arithmetic varying `Γ` inside fixed `B_PA` | First-order logic with equality; theorem/refutation domains, semantic comparison, all consistent c.e. PA extensions, and uniform independent sentences. |
| Miller instance | `E_a`; deduction in `D_a=Tot(Split(E_a))` | First-order logic with equality; an expanded real-closed-field theory, with incompleteness for the specified uniform representation-independent semidecidable extensions. |
| Cosheaf instance | `R_X`; total setting equivalent to `C_rec^J` | Propositional logic; an internal theorem subfunctor and two essentially incomplete endpoint theories. |
| Numerical foundation and second arithmetic realization | `Rec`; total setting `C_rec` | Explicit first-order/derivation realization and a source-inseparability arithmetic proof. Also supplies Section 9's computable base category. |
| Auxiliary all-model interpretation | Appendix D's faithful family `F_T` | A representation result and theory-extension comparison. The main fixed-category arithmetic soundness argument does not require all models. |

