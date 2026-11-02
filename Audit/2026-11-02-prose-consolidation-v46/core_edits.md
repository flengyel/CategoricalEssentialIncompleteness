# Core prose pass, Version 46

Manuscript: *Logical consequence and essential incompleteness in recursion categories*, Version 46, 2 November 2026.

Scope: abstract; Introduction; Categorical preliminaries; Diagonal comparison and complementary conditionals; Internal theories and semantic consistency; Appendices C and D. Read these seven sources completely before editing and reread their revised continuous prose afterward. No whole-paper correctness judgment is made here.

## Source and actual outline

Read the supplied KLR text at `tmp/review_sources/klr.txt`, §1, including points 5, 10–17, 23–26, and the definition-placement and display discussions in §§4–5. Verified principles used: connect formulas with prose; preserve self-contained theorem statements; keep notation consistent; display important formulas; avoid unnecessary jargon. The preference for inline mathematics by default comes from the user's instruction, not from a claimed categorical prohibition of displays in KLR.

The actual main-file order is: Introduction; Categorical preliminaries; Diagonal comparison and complementary conditionals; Internal theories and semantic consistency; The syntactic recursion category (including its syntax subsections); Interpretation and soundness; Essential incompleteness of arithmetic; Miller sequences and essential incompleteness; A recursion category from a three-point space; Appendices A–D; bibliography. No reorganization is proposed.

Assigned outline and function:

- Abstract: construction and the three essential-incompleteness applications.
- Introduction: DPH's problem; the two computational criteria; arithmetic, Miller-sequence, and cosheaf applications; roadmap; related work.
- Categorical preliminaries: partial maps and restriction idempotents; products, coproducts, and local connectedness; recursion and Turing categories.
- Diagonal comparison: comparison theorem and lifted-separator consequence; complementary conditionals; joins as a sufficient condition.
- Internal theories: generated sentence theories and interpretation by chosen splittings; semantic-consistency comparison; source inseparability and extensions.
- Appendix C: a recursion category showing the necessity of lifting and the failure of joins of arbitrary disjoint partial morphisms.
- Appendix D: faithful families; strict compatibility with theory extension; inseparable pairs under extension; numeral observations; a complete ambient theory.

The main dependency chain within this scope is restriction-category notation → comparison theorem → logical comparison; separately, source inseparability → consistent-extension incompleteness. Appendix C supplies a counterexample to omitting the lift. Appendix D applies the model-pair result and retains the extension argument.

## Implemented edits

| Location | Issue and rationale | Repair |
| --- | --- | --- |
| Introduction, opening and roadmap | Unneeded evaluative modifiers | Removed “principal” and “auxiliary.” |
| Introduction, inseparability antecedents | Adjacent sentences repeated “supply” and announced antecedents separately | Consolidated into “Building on these recursion-theoretic antecedents, we construct …”; retained all author credits and citations. |
| Preliminaries, restriction idempotents | Repeated “These morphisms are called” | Combined the modern and earlier terminology in one sentence. |
| Preliminaries, completion | Sentence joining objects and morphisms was grammatically incomplete | Gave the objects and morphisms separate complete sentences; retained both arrow types and the defining equation. |
| Comparison-section opening | Repeated “target pair” and separate announcement of the same construction | Connected the lift, total source morphism, and zero inverse images in one sentence; preserved the reverse order and source/target distinction. |
| Preliminaries, comparison, internal-theory sections, Appendices C–D | Short unnumbered formulas interrupted prose without requiring display | Moved 21 display blocks inline. Retained central constructions, paired comparison identities, substantial derivations, case definitions, diagrams, and both numbered observation equations as displays. |

The abstract required no edit after the paragraph-function and qualification checks. The introduction's DPH methodological distinctions, construction credits, and literature comparisons remain. In particular, the Cockett predicate/conclusion comparison remains. No theorem or counterexample was removed.

## Paragraph-function audit

Numbers below follow prose blocks separated by blank lines, excluding headings; a statement and the immediately following proof are one block if no blank line separates them. All 73 such blocks have a mathematical function. The abstract is one LaTeX paragraph with four application/construction passages.

| File | Paragraph functions, in order |
| --- | --- |
| Abstract (1) | 1 construction, contribution, and three qualified applications. |
| Introduction (13) | 1 problem and contribution; 2 DPH methodological motivation; 3 construction of sentence theories; 4 comparison of the two criteria; 5 arithmetic application; 6 Miller application and uniform-oracle restriction; 7 cosheaf application and nonequivalence; 8 dependency roadmap; 9 categorical antecedents; 10 inseparability antecedents and present construction; 11 Turing-category/incompleteness comparison; 12 introspective-theory comparison; 13 Miller-sequence antecedent. |
| Preliminaries (12) | 1 restriction categories, totality, and functors; 2 order, joins, zeros, and inseparability; 3 inverse images and ranges; 4 splitting and completion; 5 Karoubi envelope; 6 restriction products; 7 restriction coproducts; 8 range functors and a product counterexample; 9 connectedness, partial monomorphisms, and sections; 10 prodominical/isotypical categories; 11 Turing morphisms and recursion categories; 12 restriction terminal objects and Turing categories. |
| Diagonal comparison (9) | 1 construction's purpose; 2 summand notation; 3 comparison theorem and diagonal construction; 4 proof by inverse-image comparison and contradiction; 5 lifted-separator corollary and proof; 6 complementary-conditional corollary and summand identities; 7 separator contradiction; 8 disjoint-join proposition and proof; 9 counterexample reference. |
| Internal theories (12) | 1 generated sentence-theory construction and definitions; 2 interpretation by chosen splittings; 3 range preservation; 4 coproduct and join preservation; 5 interpretation proposition and image proof; 6 soundness application; 7 logical-comparison theorem and reduction step; 8 incompleteness contradiction; 9 source-criterion motivation; 10 extension corollary and proof; 11 passage to the restriction splitting; 12 application dependencies and axiom monotonicity. |
| Appendix C (14) | 1 counterexample objective; 2 numberings and coding; 3 category and morphism definitions; 4 functor definition; 5 indexed morphism representation; 6 counterexample proposition; 7 composition, restrictions, and zeros; 8 products and coproducts; 9 ranges and idempotent joins; 10 Turing construction and uniform parameterization; 11 functor preservation and target joins; 12 separated diagonal pair; 13 nonrecursive conditional and absent lift; 14 failure of a common upper bound. |
| Appendix D (12) | 1 models on a fixed carrier and numeral distinction; 2 product category and faithful-family functor; 3 preservation/faithfulness theorem and proof; 4 splitting and local connectedness; 5 weak choice, joins, and nonzeroness; 6 source/target connectedness distinction; 7 strict theory-extension square and composition laws; 8 inseparable-pair corollary and extension proof; 9 failure to preserve the Turing property; 10 target separators versus lifted source sections; 11 numeral observations and equivalences; 12 complete-theory example limiting the inference to ambient-theory incompleteness. |

## Checks and deferred candidates

- All labels and all `ref`/`eqref` occurrences in the seven files are unchanged from the saved pre-pass copies.
- All numbered `equation` environments are byte-identical.
- Compared the sequence of mathematical source content before and after, normalizing display/inline delimiters, spacing, punctuation, and `longrightarrow` versus `to`: equal for every assigned file. This is a content-preservation check, not a mathematical certification.
- Reread all revised sources continuously, including body and appendix types, total/partial distinctions, quantifiers, finite/uniform restrictions, strict commutativity, negative results, and the preserved Appendix D.2 reference to `cor:model-pair` plus its theory-extension argument.
- No definitions were relocated, no bibliography entries or citations changed, and no new terminology or editorial text was inserted into the manuscript.
- The root agent will compile the combined manuscript and inspect the rendered result after parallel edits settle; I did not compile this partial tree.
- Deferred further cuts: the abstract, DPH methodological discussion, source/target negative distinctions, end-of-section application dependencies, and Appendix D's target-separator discussion were retained because they state scope, compare genuinely different hypotheses, or explain an inference. No suspected mathematical gap was identified in the prose pass; no mathematical correctness audit was undertaken.
