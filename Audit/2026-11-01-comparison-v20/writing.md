# Independent Mathematical Writing review — version 20

Manuscript: *Logical consequence and essential incompleteness in recursion categories*, version 20, 61 pages. Source assembly: `output/manuscript/local_connectedness/main.tex`; reviewed commit `c182b1b2c54af499e0ef6f3f7ae6f179eaa55b65`. PDF page numbers below are the manuscript's numbered pages.

## 1. Overall diagnosis

The new comparison theorem is present as **Theorem 3.1, p. 5**, in **§3.1, “The comparison theorem.”** Its containing section is **§3, “Diagonal comparison and lifted partial conditionals,” pp. 4–7**. This is a clear and adequate location. The distinct application to interpreted sentence theories is **Theorem 4.2, p. 9**, in **§4.2, “Incompleteness from semantic consistency.”** The two results should not be described interchangeably: Theorem 3.1 is the categorical comparison; Theorem 4.2 applies it to a sentence-theory restriction idempotent.

The organization and mathematical prose of newly revised §§3–4 are substantially coherent. Definitions are introduced before use, the source and target categories are kept distinct, and the proof-conclusion object is distinguished from its restriction to sentence conclusions. Proposition 4.1 explicitly states a factorization condition through a validity subobject; it does not silently establish soundness for a concrete interpretation.

The principal remaining organizational issue is **unfinished integration with the later applications**. No later section cites Theorem 4.2. The applications in §§5, 9, and 10 retain the source-inseparability route through Theorem 3.5 and Corollary 4.3. Sections 7–8 retain the model functor and faithful-family construction. This accurately describes the present revision stage; it is not a counterexample to the new theorem or a reason to reject its proof. The next revision must establish the concrete interpreted-proof factorization and connect it to the new comparison route before the introduction claims that route as an accomplished application.

A limited terminology cleanup is justified in the older application sections. Several occurrences of “admissible domain monomorphism” use a second name for the partial-inverse property now explicitly defined as a restriction monomorphism. Other prose suggestions below are optional economies, not mathematical defects.

## 2. Actual outline and functions

| Part | Existing organization and mathematical function |
|---|---|
| §1, pp. 1–3 | Introduction and related work: positioning and overview. Revision deferred by instruction. |
| §2, pp. 3–4 | Partial maps, restrictions, ranges, splittings; products, coproducts, local connectedness; recursion categories. Supplies the language for §3. |
| §3, pp. 4–7 | §3.1: Theorem 3.1 and lifted-separator Corollary 3.2. §3.2: connectedness lemma, partial-section construction, source-inseparability Theorem 3.5. §3.3: disjoint joins as a sufficient lifting mechanism. |
| §4, pp. 7–10 | §4.1: sentence-theory ranges, extension of the interpretation to chosen splittings, Proposition 4.1. §4.2: semantic consistency and Theorem 4.2. §4.3: source-inseparability Corollary 4.3 and its application to theory extensions. |
| §5, pp. 10–16 | Miller computation category, the two cut-index sets, categorical realization in its total splitting, and the real-closed-field application, Theorem 5.6. |
| §6, pp. 16–28 | Construction of the syntactic recursion category. §6.1: total splitting and search. §6.2: parameterized syntax and list initiality. §6.3: free variables and substitution. §6.4: derivations and generated theories, culminating in Theorem 6.9. |
| §7, pp. 28–29 | Interpretation in a model and preservation properties, Proposition 7.1. |
| §8, pp. 29–31 | Faithfulness of the family of model interpretations, then lifting and the associated source pair. |
| §9, pp. 31–35 | Arithmetic realization, categorical reductions, essential incompleteness; numeral instances and theory extension. |
| §10, pp. 35–42 | Three-point recursion category, local connectedness, evaluation functors, propositional syntax and component theories, observation theorem and consequence. |
| Appendix A, pp. 42–50 | A.1: categorical hypotheses and Boolean notation. A.2: terms, formulas, free variables. A.3: admissible substitution. A.4: inference and deductively closed subobjects. A.5: first-order theories and the regular-image/range bridge. A.6: propositional theories. |
| Appendix B, pp. 50–58 | Cosheaf equivalence and total category; partial maps, ranges and connectedness; universal object and frame; Turing morphism; recursion-category and splitting results. |
| Appendix C, pp. 58–60 | Counterexample showing why source inseparability needs the section-lifting hypothesis. |
| Bibliography, pp. 60–61 | Literature dependencies. |

Appendix A's six-part order serves its stated job. The generic closure theorem precedes its first-order and propositional instances. Numerical realization proofs remain where the appendix is applied. Repetition of ambient hypotheses in Appendix A is warranted by the requirement that it be self-contained.

## 3. Findings and governing principles

The review used the installed `mathematical-writing:revise-mathematical-prose` skill and the supplied text of Knuth, Larrabee, and Roberts, *Mathematical Writing* (`tmp/review_sources/klr.txt`). The relevant advice is §1, items 5, 10–15, 17, 24, and 26; the discussion of definition timing and useful explanation in §4, pp. 9–10; and the discussion of excessive parenthetical nesting in §5, p. 11. These support judgments about exposition; they do not prove or disprove the mathematics.

| Priority and anchor | Finding | Source-grounded principle | Recommended action |
|---|---|---|---|
| Integration; §§7–9, relative to Theorem 4.2 | The new abstract theorem has no later concrete invocation. The current soundness paragraph after Proposition 4.1 states what a proof of soundness would supply. | §1, items 10–13: explain the connection between results and the argument they support. | Establish the intended concrete proof-object interpretation and validity factorization in the application section; then give the explicit invocation of Theorem 4.2. Do not present the abstract criterion itself as the completed concrete soundness proof. |
| Terminology clarification; Proposition 5.5, p. 14; Proposition 9.1, p. 32 | “Admissible domain monomorphism” is not separately specified there; the proofs establish the partial-inverse property already named in §4.1. | §1, items 14 and 26: consistent terminology; avoid unnecessary new jargon. | Use “restriction monomorphism” with its ambient restriction splitting, or state the partial-inverse property directly. Preserve the distinction between a category and one equivalent to it. |
| Optional terminology economy; Appendix B, p. 53 | “Total restriction embedding” is explicitly defined, but its defining equations repeat the restriction-monomorphism condition. This is not an undefined term. | §1, items 14 and 26. | Consider using “restriction monomorphism into \(V\)” throughout this construction. Keep the universal-object lemma and proof. |
| Optional prose economy; §6, p. 17; Appendix C, p. 58 | “Actual sets” and “actual domain” add no mathematical distinction beyond the formulas and surrounding sentences. | §1, item 17; the skill's instruction to remove unnecessary contrast. | Delete “actual.” This is a minor cleanup. |
| Deferred; introduction, p. 2 | The roadmap attributes an incompleteness corollary to §3, although its internal-theory form is now in §4. The appendix description begins with the cosheaf construction although syntax is now Appendix A. | §1, items 10 and 14: accurate organization and consistent references. | Correct when the introduction is revised last, as requested. Do not revise it during this pass. |

I found no need to rename “comparison theorem.” The displayed source-to-target comparison makes the name intelligible. Theorem 4.2's subsection heading distinguishes its purpose, so an additional theorem caption is optional, not a required correction.

## 4. Definition-order, notation, and typing audit

The following checks passed at the level of exposition and declared types:

- In §4, \(\mathscr S=\operatorname{Split}(\mathscr R)\) and \(\mathcal D=\operatorname{Tot}(\mathscr S)\) precede the syntax objects. The formula object, sentence subobject, axiom subobject, and proof-conclusion map have explicit ambient categories and arrows.
- The pullback \(P_{A,S}\) separates sentence conclusions from arbitrary formula conclusions. The regular image of \(c_{A,S}\), its assumed partial inverse, and the resulting restriction idempotent are displayed in the correct order.
- The chosen-splitting extension \(\widehat F\) is defined before its use. Its restriction to source objects and the preservation statements needed in Theorem 4.2 are supplied before that theorem.
- Theorem 3.1 states its own categorical data, diagonal pair, target domains, conditional and lift. Theorem 4.2 refers precisely to those data and supplies its additional hypotheses; this is a reasonable dependent theorem statement, not an unexplained appeal to “the usual assumptions.”
- Appendix A places \(V\) in \(\mathcal D\), gives the required decidable equality and categorical structure, and specifies the syntax functors and their algebras. The named-variable syntax includes quantifiers, free-variable lists, admissibility and substitution.
- Appendix A's Boolean operations are defined through coproduct/copairing constructions and checked by equations. The conditional copairing and the bold \(\mathbf t,\mathbf f\) notation serve the user's requested distinction. Keep the calculations; their elementary nature is not a reason to delete them.
- Appendix A explicitly explains finite product powers. There is no basis for an objection that the notation presupposes exponentials.
- “Structural recursion,” “initial algebra,” “fold,” “range,” and “source” are used in their mathematical senses. They are not instances of invented or non-mathematical terminology.

No editorial discussion of review passes, revision history or process was found in the mathematical source. Negative mathematical statements about failed composition, failure to preserve a Turing morphism, or failure of lifting explain mathematical limits and must not be removed as “defensive prose.”

## 5. Organizational recommendation

Retain the placement and order of §§2–4 and Appendix A. A new wholesale outline is not warranted by this writing review. The next body revision should connect the existing syntactic realization in §6 to an interpretation of its proof object in §7, prove the required validity factorization, and then state the concrete use of Theorem 4.2. Reassess the role and placement of the faithful-family material in §8 after that mathematical dependency is established. Only then revise the application narratives and, last, the introduction and abstract.

This recommendation concerns the argument's exposition. Whether a particular interpretation supplies the full factorization, and whether the lifting assumptions are available, must be decided by the mathematical review; prose changes cannot discharge those obligations.

## 6. Exact replacement suggestions

These are proposed edits for the reducer to evaluate; no manuscript file was changed.

1. `sections/04-miller-sequences.tex:322–324`, Proposition 5.5:

   > Every monomorphism of \(\mathcal D_a\) has a partial inverse in \(\operatorname{Split}(\mathcal E_a)\), and there is a restriction equivalence …

   At the proof's corresponding conclusion, lines 362–364:

   > Thus every monomorphism of \(\mathcal D_a\), regarded in the restriction splitting, is a restriction monomorphism.

   At line 470:

   > The realization proposition supplies a partial inverse for this image monomorphism.

2. `sections/08-essential-incompleteness-of-arithmetic.tex:75–77`, Proposition 9.1:

   > Under the displayed equivalence, every monomorphism of \(\mathcal C_{\mathrm{rec}}\) corresponds to a restriction monomorphism in \(\operatorname{Split}(\mathrm{Rec})\), and …

   At lines 113–114, the proof already says that preimage search provides a partial recursive inverse on the image. The following “Hence every such monomorphism is an admissible domain inclusion up to isomorphism” can simply be deleted: the next sentence constructs the span interpretation directly from that inverse.

3. Optional, `appendices/b-three-point-cosheaves.tex:271–275`:

   > A restriction monomorphism \(m:Y\to V\) in \(\mathcal A\) is a total morphism with a partial inverse …

   Retain the equations and change the two later instances of “total restriction embedding” consistently. This unifies terminology while preserving the appendix's local explanation.

4. Optional, `sections/05-syntactic-recursion-category.tex:109`:

   > Montagna's objects are the sets generated from \(\mathbb N\) by …

   Optional, `appendices/c-section-lifting.tex:42`:

   > Here \(\simeq\) includes simultaneous undefinedness: the domain …

No general simplification of the substitution or initiality proofs is recommended. Their domain conditions and parameter dependence are part of the construction, not expository clutter.

## 7. Scope and limits

Read all assembled manuscript source, including both front-matter files, all ten numbered sections, all three appendices and the bibliography. Cross-reference numbers and page anchors were checked against the compiled auxiliary file; full proof-source reading was used to evaluate organization, definition order and notation. Read the actual supplied KLR source, rather than relying only on the skill's summary.

This review does not certify every proof, establish the missing concrete interpretation, independently verify every literature attribution, or certify the rendering of every PDF page. Bibliographical precedents already present in Appendix A were not proposed for removal merely because the appendix has one task. Introductory and abstract changes remain deferred. No manuscript edits or commits were made.
