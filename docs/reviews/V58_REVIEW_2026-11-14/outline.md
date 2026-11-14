# Functional outline and front-matter comparison — manuscript v58

Source: current `revision-v58/manuscript/latex/`, *Logical consequence and essential incompleteness in recursion categories*, Version 58, 14 November 2026. This report records the final edited source before remote synchronization. The existing 67 headings were checked against the current input graph before the body reread. The outline follows `main.tex` and nested inputs, not filename order. The literal inventory contains 14 sections and 53 subsections; its nested `\texorpdfstring` title is corrected below. Pages are the PDF/printed manuscript pages (they coincide). Result pages are indexed from the final `main.aux`.

## Central question and contribution

Starting with categorical partial computation, which additional categorical hypotheses construct internal finite deduction, and when does a computational inseparable pair force every consistent extension of the resulting theory to be incomplete? The paper supplies generic syntax and generated-theory constructions, two incompleteness criteria, generation/translation adjunctions, associated partial-slice categories and transfer, then arithmetic, Miller and cosheaf realizations. These are distinct from starting with an arithmetic theory and representing computation in it.

## Existing outline and function

| Level | Heading | Source anchor | Function |
|---|---|---|---|
| section | Introduction | `sections/01-introduction.tex:1` | Problem, contribution, hypotheses, application scope and roadmap. |
| subsection | Related work | `sections/01-introduction.tex:138` | Literature comparison: categorical foundations, inseparability, modal motivation, Turing categories and Miller realizability. |
| section | Categorical preliminaries | `sections/02-categorical-preliminaries.tex:1` | Definitions and conventions used by all subsequent proofs. |
| subsection | Partial maps and restriction idempotents | `sections/02-categorical-preliminaries.tex:3` | Defines partial morphisms, restrictions, order, ranges, splitting and partial-map categories. |
| subsection | Products, coproducts, and local connectedness | `sections/02-categorical-preliminaries.tex:104` | Defines restriction products/coproducts, range functors, local connectedness and weak choice; gives the non-preservation-of-products example. |
| subsection | Recursion categories | `sections/02-categorical-preliminaries.tex:164` | Defines recursion and Turing categories and fixes their relation. |
| section | Diagonal comparison and complementary conditionals | `sections/03-sections-and-inseparability.tex:1` | Computational comparison theorem and the source condition needed for inseparability. |
| subsection | The comparison theorem | `sections/03-sections-and-inseparability.tex:15` | Constructs a total parameter morphism avoiding both disjoint target domains; proves noncoverage. |
| subsection | Complementary conditionals | `sections/03-sections-and-inseparability.tex:96` | Obtains source inseparability from complementary conditionals and constructs such conditionals using joins. |
| section | Internal theories and essential incompleteness | `sections/03a-internal-theories.tex:1` | Converts computation into internal deduction and compares generated theories. |
| subsection | Theories and their interpretation | `sections/03a-internal-theories.tex:3` | Defines generated sentence theories and their interpretation; extends range functors through splitting. |
| subsection | Incompleteness from semantic consistency | `sections/03a-internal-theories.tex:138` | Applies the computational comparison to a sound interpreted theory (Theorem 4.2). |
| subsection | Inseparability in the source | `sections/03a-internal-theories.tex:197` | Uses reduction of a fixed inseparable pair to prove every consistent extension incomplete (Corollary 4.3). |
| subsection | Generation and logical translations | `sections/03b-internal-adjunctions.tex:1` | Proves generation reflection, logical-translation Galois connections and their composition laws (4.4–4.5). |
| subsection | Change of the ambient category | `sections/03b-internal-adjunctions.tex:156` | Proves the comparison square for generation under a regular functor (4.6). |
| subsection | Free first-order theories and inseparability | `sections/03b-internal-adjunctions.tex:255` | Constructs the free signed first-order theory and adjunction; proves essential incompleteness iff inseparability (4.7–4.8). |
| section | Theory extensions and recursion categories | `sections/04-theory-extensions.tex:1` | Associates partial-map categories to theories, then proves functoriality and transfer of incompleteness. |
| subsection | Categories associated with internal theories | `sections/04-theory-extensions.tex:8` | Defines C[T], its slice Turing morphism and the full recursion subcategory R[T] (5.1). |
| subsection | Functoriality under theory extension | `sections/04-theory-extensions.tex:87` | Proves fully faithful postcomposition, two adjunctions, properness and the sentence/theorem square (5.2). |
| subsection | Essential incompleteness in the associated category | `sections/04-theory-extensions.tex:162` | Constructs constant families and a fibre retraction; proves essential-incompleteness and no-total-extension equivalences (5.3). |
| section | The syntactic recursion category | `sections/05-syntactic-recursion-category.tex:1` | Constructs the syntactic recursion category S_T with uniform T-provable equality and distinguishes the invalid primed quotient. |
| subsection | The total restriction splitting | `sections/05a-internal-syntax.tex:1` | Proves predicate presentation, regularity, stable coproducts and partial inverses of monos (6.2–6.3). |
| subsection | Syntax and lists | `sections/05a-internal-syntax.tex:292` | Constructs arithmetic syntax/list initial algebras with arbitrary parameters (6.4–6.6). |
| subsection | Free variables and substitution | `sections/05a-internal-syntax.tex:522` | Identifies finite-code free-variable and admissible-substitution operations with the categorical folds (6.7). |
| subsection | Derivations and theories | `sections/05a-internal-syntax.tex:652` | Constructs initial finite-derivation algebras and generated sentence theory idempotents (6.8–6.9). |
| section | Interpretation and soundness | `sections/06-interpretation-in-models.tex:1` | Builds model interpretations and proves the soundness needed for arithmetic comparison. |
| subsection | Lifting complementary conditionals | `sections/06-interpretation-in-models.tex:58` | Constructs total conditionals in S_T and source inseparability (7.2–7.3). |
| subsection | The total interpretation functor | `sections/06-interpretation-in-models.tex:119` | Identifies the total interpretation with predicate evaluation and proves regularity (7.4). |
| subsection | Soundness on standard codes | `sections/06-interpretation-in-models.tex:161` | Distinguishes code model N from semantic model K, proves semantic substitution and soundness (7.5–7.6). |
| subsection | Ultrapowers of the interpretation functor | `sections/06-interpretation-in-models.tex:337` | Constructs ultrapower functor, its natural comparison with G_M and soundness transfer (7.7–7.9). |
| section | Essential incompleteness of arithmetic | `sections/08-essential-incompleteness-of-arithmetic.tex:1` | First application: arithmetic incompleteness, uniformity, numerical comparison and associated categories. |
| subsection | Comparison in the fixed syntactic category | `sections/08-essential-incompleteness-of-arithmetic.tex:3` | Reduces the diagonal pair to provability, constructs the lifted conditional, proves incompleteness and recursive inseparability (8.1–8.4). |
| subsection | An indexed family of arithmetic theories | `sections/08a-uniform-theories.tex:1` | Constructs one theory/derivation family and identifies each numeral fibre (8.5). |
| subsection | Uniform independent sentences | `sections/08b-uniform-independent-sentences.tex:1` | Constructs a single total sentence morphism giving an independent sentence for each consistent indexed theory (8.6). |
| subsection | The numerical realization | `sections/08c-numerical-realization.tex:1` | Builds the numerical category and syntax/proof comparison, with equality of sentence-theory images (8.7–8.8). |
| subsection | Numerical incompleteness | `sections/08d-numerical-incompleteness.tex:1` | Applies Corollary 4.3 in the numerical recursion category. |
| subsection | Numeral instances and theory extension | `sections/08-essential-incompleteness-of-arithmetic.tex:271` | Packages provability of numeral instances as a functor into pairs and compares Bernardi’s argument. |
| subsection | The associated recursion categories | `sections/08-essential-incompleteness-of-arithmetic.tex:312` | Constructs the separate free signed theory on the arithmetic diagonal pair and instantiates §5 (8.9–8.10). |
| section | Miller sequences and essential incompleteness | `sections/04-miller-sequences.tex:1` | Second application: a representation-independent recursion category from a Miller sequence. |
| subsection | Computation independent of the binary representation | `sections/04-miller-sequences.tex:41` | Constructs unanimous evaluation and proves the recursion-category axioms (9.1–9.2). |
| subsection | The index sets below and above 1/2 | `sections/04-miller-sequences.tex:171` | Constructs a recursive reduction to strict cuts at 1/2; distinguishes internal inseparability from fixed-oracle separation (9.3–9.4). |
| subsection | A theory of real closed fields | `sections/04-miller-sequences.tex:277` | Builds internal field syntax, parameterized derivations and the expanded real-closed-field theory; proves incompleteness (9.5–9.7). |
| subsection | The associated recursion categories | `sections/04-miller-sequences.tex:531` | Instantiates §5 for each consistent internal extension of the Miller field theory (9.8). |
| section | A recursion category from a three-point space | `sections/09-three-point-space.tex:1` | Third application: the cosheaf/fork recursion category and its propositional and first-order theories. |
| subsection | Complementary restriction idempotents and inseparability | `sections/09-three-point-space.tex:144` | Constructs source conditionals and deduces internal inseparability. |
| subsection | Evaluation functors | `sections/09-three-point-space.tex:176` | Proves preservation for endpoint functors, their Turing property and the failure at the central component (10.1). |
| subsection | Propositional theories and component theorem sets | `sections/09-three-point-space.tex:273` | Constructs initial propositional syntax/derivations, consistent component theories and endpoint essential incompleteness (10.2–10.6). |
| subsection | First-order theories in the functor category | `sections/09-three-point-space.tex:614` | Constructs first-order syntax for arbitrary nullary labels and proves conservativity and endpoint consequences (10.7–10.8). |
| subsection | Categories associated with theory extensions | `sections/09-three-point-space.tex:779` | Instantiates §5 for the first-order fork theory (10.9). |
| section | Syntax and deductively closed theories | `appendices/a-syntax-and-theories.tex:1` | Generic syntax and deduction construction used by the main theorems and all realizations. |
| subsection | Categorical hypotheses and notation | `appendices/a-syntax-and-theories.tex:10` | Lists regular/extensive and parameter-stable initiality hypotheses; defines Boolean and variable conventions. |
| subsection | Terms, formulas, and free variables | `appendices/a-syntax-and-theories.tex:156` | Defines the polynomial syntax algebra, occurrence lists and sentence subobject. |
| subsection | Admissible substitution | `appendices/a-syntax-and-theories.tex:274` | Constructs capture-avoiding admissible substitution by parameterized initiality (A.3). |
| subsection | Inference rules and deductively closed subobjects | `appendices/a-syntax-and-theories.tex:407` | Defines the inference endofunctor and proves the least closed image theorem (A.4–A.5). |
| subsection | First-order theories | `appendices/a-syntax-and-theories.tex:489` | Specifies seven first-order schemes and two rules, generated sentence theories and range/image comparison (A.6–A.7). |
| subsection | Propositional theories | `appendices/a-syntax-and-theories.tex:637` | Specializes the generic deduction construction to propositional logic. |
| section | The three-point cosheaf construction | `appendices/b-three-point-cosheaves.tex:1` | Detailed cosheaf/fork construction supporting §10. |
| subsection | Cosheaves and functor categories | `appendices/b-three-point-cosheaves.tex:3` | Proves the cosheaf equivalence, regular/extensive total category and component image formulas (B.1–B.2). |
| subsection | Partial maps, ranges, and connected restriction idempotents | `appendices/b-three-point-cosheaves.tex:118` | Constructs the partial-map restriction structure, joins and local connectedness (B.3–B.4). |
| subsection | A universal object and a frame | `appendices/b-three-point-cosheaves.tex:233` | Builds universal embeddings and frame isomorphisms (B.5–B.6). |
| subsection | A Turing morphism | `appendices/b-three-point-cosheaves.tex:322` | Constructs a natural Turing morphism with exact component domains and proves its universal property (B.7). |
| subsection | The recursion category and its splitting | `appendices/b-three-point-cosheaves.tex:471` | Builds the recursion subcategory, splitting/Karoubi equivalences and distinction from Rec (B.8–B.10). |
| section | Necessity of section lifting for inseparability | `appendices/c-section-lifting.tex:1` | Counterexample showing that section lifting cannot be omitted; separates joins of idempotents from joins of arbitrary partial morphisms (C.1). |
| section | Faithful model interpretations and theory extension | `appendices/d-faithful-family.tex:1` | Faithful family of all countable arithmetic model interpretations; separates semantic faithfulness from preservation of universality. |
| subsection | Inseparable pairs under theory extension | `appendices/d-faithful-family.tex:84` | Proves preservation of diagonal inseparability under extension quotients (D.2). |
| subsection | Provability of numeral instances | `appendices/d-faithful-family.tex:131` | Relates provability of numeral instances to the faithful family, without claiming join preservation. |
| subsection | The theory of the standard model | `appendices/d-faithful-family.tex:158` | Exhibits complete Th(N) with categorical inseparability, bounding what source inseparability alone implies. |

## Main dependencies

| Result group | Required constructions/results | Role |
|---|---|---|
| 3.1–3.4 | §2 restrictions, ranges, coproducts, Turing parameterization | Computational comparison and source inseparability. |
| 4.1–4.3 | Appendix A generated theory; range/image comparison; §3 | Soundness-based comparison and inseparable-pair criterion. |
| 4.4–4.8 | Appendix A syntax/derivation initiality; regular images; 4.3; partial inverses | Generation reflection, translations, free signed theory and converse via Boolean valuation. |
| 5.1–5.3 | Restriction splitting; all-mono partial inverses; 4.3; parameterized deduction; global logical theorem for 5.3 | Associated categories, extension functors and transfer. The slice Turing structure in 5.1 and the categorical functor in 5.2 do not require syntax; syntax is needed for the internal-theory comparison. |
| 6.1–6.9 | Montagna/Di Paola–Montagna computation coding; PA; Appendix A | Concrete syntactic realization of the generic hypotheses. |
| 7.1–7.9 | §6; first-order soundness; ultrapowers | Interpretation and semantic consistency. |
| 8.1–8.6 | §6–7; 3.1/4.2; coded diagonal pair | Arithmetic comparison, recursive inseparability and uniform independent sentences. |
| 8.7–8.10 | Numerical equivalence; Appendix A; 4.3/4.8; §5 | Numerical incompleteness and separate arithmetic signed-theory instance. |
| 9.1–9.8 | Miller property; effective compactness; oracle parameterization; Appendix A; 4.3; §5 | Representation-independent field-theory application. |
| 10.1–10.9 | Appendix B fork category; Appendix A finite deduction; 4.3; §5 | Propositional/first-order cosheaf application. |
| Appendix C | Computation relative to the halting set; §2–3 definitions | Necessity of the lifting hypothesis. |
| Appendix D | §6–7 and all countable models of T | Faithful family, extension square and limit of inseparability alone. |

Appendix A and Appendix B are explicit forward dependencies. The text points to them before using their constructions; the dependency order is not circular. No reordering of whole sections is needed.

## Abstract comparison

The abstract is one paragraph, so the following rows are consecutive sentence units rather than invented paragraphs.

| Unit / source | Function / advertised claim | Body support and assessment |
|---|---|---|
| A1, `abstract.tex:2` | Arithmetization motivation | Accurately states the direction reversed by the paper. Retain. |
| A2, `abstract.tex:3–5` | Computation-first construction | Appendix A and concrete §§6,9,10. Retain. |
| A3–A4, `abstract.tex:5–9` | Categorical existence hypotheses | Appendix A, §4 and §5 state the necessary structures. The abstract gives a sufficient package, not a minimal-hypothesis claim. Retain. |
| A5, `abstract.tex:9–11` | Inseparable-pair criterion for all consistent internal extensions | Corollary 4.3. Retain. |
| A6, `abstract.tex:11–13` | Generation adjunction and translation Galois connections | 4.4–4.5. Retain. |
| A7, `abstract.tex:13–14` | Fully faithful functors between associated Turing categories | 5.1–5.2. Retain. |
| A8, `abstract.tex:14–16` | Preservation/reflection of essential incompleteness | 5.3. The revised sentence states the equivalence for the constant family in the associated category. It removes the v57 referent ambiguity and preserves the hypotheses. |
| A9, `abstract.tex:16–18` | Di Paola–Heller objective | Consistent with §1 motivation and the scope of the construction. Retain. |
| A10–A12, `abstract.tex:18–24` | Arithmetic internal and external incompleteness, uniformity | 8.3,8.4,8.6. Retain all three distinctions. |
| A13–A14, `abstract.tex:24–27` | Miller field theory and common-program axiom enumeration | 9.5–9.7. Matches representation-independent domain/value condition. Retain. |
| A15–A16, `abstract.tex:28–31` | Two endpoint propositional theories and first-order extensions | 10.6,10.8. Retain. |
| A17, `abstract.tex:31–34` | Three associated-category instances | 8.10,9.8,10.9. The distinct arithmetic signed theory is correctly named. Retain. |

## Introduction paragraph comparison

| Paragraph / source | Function | Comparison with body |
|---|---|---|
| I1, lines3–9, p1 | Central contribution and Di Paola–Heller motivation | Matches generic deduction and incompleteness results; no proof imported. |
| I2, lines11–24, pp1–2 | Hypotheses, sentence image, consistency and completeness | Matches Appendix A and §4. The domain vocabulary is explained informally here and formally in §2. |
| I3, lines26–47, p2 | Two incompleteness criteria | Distinguishes 4.2 comparison under semantic consistency from 4.3 internal essential incompleteness. Retains partial-lift and nonzero hypotheses. |
| I4, lines49–62, p2 | Generation, translation and free signed theories | Matches 4.4–4.8; consistency is conditional in the general signed construction. |
| I5, lines64–81, p2 | Associated categories and transfer | Matches §5 and explicitly locates the Boolean morphism in the associated category. It packages categorical and internal-theory conclusions under a sufficient hypothesis. The categorical conclusions of 5.1–5.2 hold without the extra syntax assumptions; the stronger sufficient package is not false, and no replacement paragraph is proposed. |
| I6, lines83–100, pp2–3 | Arithmetic application | Correctly separates the internal arithmetic theory of 8.3 from the free signed theory of 8.9–8.10. |
| I7, lines102–113, p3 | Miller application | Matches 9.7–9.8 and common-program scope. |
| I8, lines115–125, p3 | Cosheaf application | Matches distinction from Rec, endpoints 10.6 and first-order 10.8–10.9. |
| I9, lines127–136, p3 | Roadmap | Accurate; §4’s adjunctions are covered by the section-level description, though not enumerated again. |
| R1, lines140–151, p3 | Categorical foundations | Has a stated role for each cited family. |
| R2, lines153–160, p3 | Inseparability antecedents | Directly relevant to 3.3 and §8.6; retain. |
| R3, lines162–166, p3 | Modal motivation | Brief contextual antecedent, not claimed as a proof ingredient. Retain. |
| R4, lines168–177, pp3–4 | Other Turing/categorical incompleteness work | States the differing predicate and conclusion; retain. |
| R5, lines179–183, p4 | Miller realizability antecedent | Identifies source of the representations and distinguishes the field-theory result. Retain. |

The introduction summarizes the paper rather than reproducing it. It contains no proof; the main constructions, universal properties and specializations remain in the body. Its length is justified by the two criteria and the three genuinely different applications. No wholesale rewrite or new section is recommended.

## Review state

Outline and front-matter comparison established before the v58 body reread. The reference-audit changes were rechecked and are recorded in `writing-review.md`. The final rebuilt v58 PDF has 87 pages. The updated Lemma 6.1 proof and the equality-convention passage were visually checked on pages 18 and 81; pages 1 and 14 had already been checked and retain the same passages. The completed reference audit covers 32 works and 66 citation occurrences, and the manifest selects v58.
