# Introduction organization, version 44

The introduction contains the paper's problem and contributions, but its middle develops much of the technical setup before the reader reaches the applications. It should introduce the mathematical objective, the constructions obtained, the comparison's role, and the main conclusions; the proofs' definitions and intermediate equations already have complete homes in the body. The repair is relocation or removal of duplicate exposition, with explicit endpoint names for the one comparison functor retained in the introduction.

## Actual outline

The following are logical paragraphs; a displayed image factorization is included with its surrounding paragraph.

| No. | Opening / content | Function | Recommended treatment |
|---|---|---|---|
| 1 | Di Paola–Heller introduced dominical categories; present internal systems and applications | Problem and contribution | Retain. |
| 2 | Diagonalizable algebras, GL, Hilbert–Bernays qualification, numeral/quantifier obstacles, intrinsic recursion | Historical criterion | Retain the criterion and qualification, with economical source-grounded explanation. This is needed to explain what the paper addresses. |
| 3 | Two representations of a theory; partial-function analogy; Split, Tot, regularity, syntax hypotheses | Definition/setup | Keep only the conceptual point that generated theories are represented internally in restriction-idempotent completions. Leave the tutorial and categorical hypotheses in Section 2 / Appendix A. |
| 4 | Formula object, sentence inclusion, axiom subobject, initial derivations, conclusion-image display | Construction | Remove the duplicate construction from the introduction. Section 4.1 and Appendix A state it fully. |
| 5 | Partial inverse, restriction range, negation, consistency and completeness equations | Construction/definitions | Remove the equations and local notation here. Retain the conceptual connection between deduction and computational restriction idempotents, if it is needed in the contribution paragraph. |
| 6 | First comparison argument, validity image, source reduction/lift, counterexample | Proof overview | Retain one short typed comparison overview and the fact that the lifting condition matters. Leave the sequence of intermediate morphisms and precise preservation failures in Sections 3–4 and Appendix C. |
| 7 | Fixed inseparable pair, extension monotonicity, separator pullback | Proof overview | Keep the result that the criteria apply to the represented consistent extension classes; leave the proof sequence in Section 4.3. |
| 8 | S_T definition, provable graph equality, total splitting, fixed ambient S_PA | Application setup | Keep attribution and the fixed-category/represented-theory distinction in the arithmetic result overview. Move detailed quotient and realization notation to Section 5, where the construction is developed. |
| 9 | Syntax-code/model separation, soundness induction, ultrapower transport, proof search, arithmetic and uniformity conclusions | Application plus proof chain | Keep the categorical arithmetic conclusion and uniform-independence result. Leave the code/model distinction and soundness transport in Section 6, with a short explanatory reference if needed to prevent a false soundness claim. |
| 10 | Miller sequence, category, binary representations, L_a/R_a, reduction sentence, field theory and extension class | Application construction and result | Keep Miller attribution, the representation-independent computation condition, field theory, and effective extension scope. Leave the L_a/R_a display and explicit reduction to Section 8. |
| 11 | Three-point cosheaves, category inequivalence, propositional realization, endpoint theories | Application and result | Keep the nonnumerical example and its essential-incompleteness statement, including the same-language c.e. restriction. Internal subfunctor/evaluation mechanics belong in Section 9. |
| 12 | Section-by-section roadmap | Organization | Retain a shorter roadmap, preferably after the literature comparison. |
| 13 | Inseparability objective, local-connectedness/existence history, typed F:R→A | History plus repeated present setup | Keep the historical comparison. Move the sole typed F overview to the contribution/method paragraph so that this paragraph only compares the existence question with the present task. |
| 14 | F-hat, validity condition, arithmetic F_M, model M, Appendix D product target | Repeated technical setup | Remove duplicate soundness/lift setup. The exact model and product descriptions are already in Sections 6–7 and Appendix D. If F_M is retained, its M definition must remain; easier is to retain only the generic F and describe the arithmetic interpretation in prose. |
| 15 | Rosolini, Heller, Cockett–Lack, Cockett–Hofstra and P-category equivalence | Literature infrastructure | Retain the relationships relevant to the setting. Definitions and proposition-level verification belong in Section 2. |
| 16 | Cockett's incompleteness result and distinct conclusion | Literature comparison | Retain the input/output difference, including “restriction terminal object.” |
| 17 | Di Paola–Heller, Bernardi, Montagna inseparability antecedents | Literature comparison | Retain attribution and the additional internal-deduction/theory construction. Exact older-theorem hypotheses need not all be reproduced here if the comparison does not use them. |
| 18 | Ramesh introspection definition and derived Löb | Literature comparison | Retain the fact that Löb is derived and the precise difference in constructions/results. An introduction need not reproduce the full internal-model definition. |
| 19 | Our syntax/derivation/images contribution and no postulated Löb/H–B | Repeated contribution | Consolidate with the earlier contribution/method paragraph, or use one concise sentence linking the literature comparison to that construction. |
| 20 | Miller/Bauer–Hanson comparison and present use | Literature comparison | Retain the antecedent and distinct logical application, avoiding a second outline of Section 8. |

## Existing body homes and dependency checks

No theorem, proof, hypothesis, or definition needs to be deleted from the body to shorten the introduction.

| Technical material now previewed in detail | Existing complete location |
|---|---|
| Category of total morphisms and restriction-idempotent completion | `sections/02-categorical-preliminaries.tex`, lines 24–27 and 65–87, Section 2.1. |
| Ambient regular category, formula and sentence objects, axiom inclusion, derivation conclusion morphism and sentence image | `sections/03a-internal-theories.tex`, lines 5–27, Section 4.1; categorical general construction in Appendix A, Theorem `thm:first-order-theory` at line 570. |
| Partial inverse, equality of theorem image and restriction range, negation, consistency/completeness | Section 4.1, lines 28–42; Appendix A, Lemma `lem:range-regular-image` at line 621. |
| Extension of F to the splitting and its preservation properties | Section 4.1, lines 44–91; Proposition `prop:interpreted-theory` and its following explanation, lines 94–140. |
| Reduction/lifting hypotheses and target/source incompleteness conclusions | Section 3.1, Theorem `thm:comparison`; Section 4.2, Theorem `thm:logical-comparison`, lines 144–205. |
| Fixed-pair reduction and persistence under represented extension | Section 4.3, Corollary `cor:domain-incompleteness`, lines 212–245. |
| S_T quotient and categorical syntax realization | `sections/05-syntactic-recursion-category.tex`; `sections/05a-internal-syntax.tex`, Theorem `thm:syntactic-generated-theory` at line 834. |
| Standard syntax codes versus formulas interpreted in K, finite-derivation soundness | Section 6.3 (`sections/06-interpretation-in-models.tex`, lines 165–342), Proposition `prop:standard-code-soundness`. |
| Ultrapower code interpretation and soundness transport | Section 6.4, lines 344–end, especially Theorem `thm:ultrapower-soundness` at line 453. |
| Arithmetic comparison and uniform independent sentences | Section 7.1, Theorem `thm:arithmetic-internal-comparison` at line 193; Section 7.3, Theorem `thm:uniform-independent-sentences`. |
| Miller category, index sets, reduction to field sentences | Section 8.1, Proposition `prop:miller-category`; Section 8.2, Corollary `cor:miller-cuts-inseparable`; Section 8.3, Theorem `thm:miller-incompleteness` at line 442. |
| Cosheaf endpoint/evaluation machinery and essential incompleteness | Section 9, the subsections on complementary restriction idempotents, evaluation functors, and propositional theories (`sections/09-three-point-space.tex`, lines 151–end), Corollary `cor:cosheaf-essential-incompleteness` at line 634. |
| Model-family product and functor F_T | Appendix D (`appendices/d-faithful-family.tex`), lines 3–22 and Theorem `thm:faithful`. |

## Proposed introduction skeleton

1. **Problem and historical objective.** Begin with dominical categories and the categorical generalized-incompleteness objective. State essential incompleteness in terms of the specified effective extension classes.
2. **Methodological criterion.** Explain Di Paola–Heller's demand for intrinsic recursion theory and the reason their discussion of axiomatized Löb matters. Retain the Hilbert–Bernays qualification without turning the paragraph into a modal-logic development.
3. **Present construction and comparison.** Explain that finite derivations generate internal sentence theories and that their computational representations allow recursion/inseparability arguments. Introduce one range functor F:R→A with named source recursion category R and target restriction category A; explain interpretation, target disjointness, and the necessary reduction/lifting hypotheses at the level of their mathematical role. Do not reproduce image factorizations, inverse-image equations, or split-extension formulas.
4. **Arithmetic conclusion.** Attribute S_T to Montagna and Di Paola–Montagna at its first mention. State that internal theories in the fixed PA category represent c.e. extensions and that the comparison yields their essential incompleteness. Include uniform independent sentences if this is a principal contribution. Retain the distinction between the fixed category's equality theory and represented extensions.
5. **Miller conclusion.** Attribute Miller and the representation formulation of Bauer–Hanson. State the real-closed-field result and its single-program-across-representations condition. Defer cut-index formulas and reduction maps.
6. **Cosheaf conclusion.** State the further categorical example and the two propositional theories, with the exact effective/same-language extension class. Defer endpoint mechanics.
7. **Focused literature comparison.** Retain the directly relevant antecedents and distinctions: categorical recursion/existence, Bernardi/Montagna inseparability, Cockett's different input/output, Ramesh's derived Löb and distinct internal interpretation data, and Miller/Bauer–Hanson. Avoid repeating the present construction after every author. Keep definitions attached to their technical use rather than filling the introduction with a glossary.
8. **Roadmap.** Name the major comparison, realization/soundness, application, and appendix roles without listing every intermediate lemma.

This is a functional skeleton, not a word quota or a demand for one paragraph per item. The three applications can be separate paragraphs because their hypotheses differ. Attribution at the beginning of each relevant body section will let the introduction identify the mathematical contribution without carrying those sections' full construction details.

## Governing writing source and scope

KLR §1, points 12–13, supports attention to the reader's present knowledge and exposition that remains intelligible when formulas are skimmed. Point 11 supports informal definitions of retained variables at first use; removing unused preview notation is preferable to leaving it undefined. Lamport's remarks in §31, printed pp. 69–70, concern knowing the paper's theme/audience and repairing the organization of ideas rather than only sentences. These principles support the specific relocation above; KLR does not prescribe a fixed introduction length or forbid technical formulas categorically.

Scope: complete current introduction, the relevant KLR passages, and the named body destinations. This is an organization/dependency review, not a new proof or priority audit. No manuscript files were edited.

