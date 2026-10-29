# Mathematical-writing review

Date: 29 October 2026.
Scope: the entire new LaTeX source and its 14-page rendering.
Method: author-side application of the mathematical-writing plugin, governed
by Knuth, Larrabee, and Roberts, *Mathematical Writing*.

## Source consultation

The supplied book was consulted at PDF pages 3–7 and 11–15 (printed
pages 1–5 and 9–13). These passages govern prose around formulas,
notation, definitions, and the order in which mathematical ideas are
presented. This report paraphrases their guidance; it does not quote
them or claim a complete rereading of the book.

The complete plugin workflow and its terminology and source-review
references were consulted. The plugin supplies instructions, not an
independent editorial service; this is a review by the drafting assistant.

## Argument and organization

The paper states its target first: recognize the finite constructor stages
by termination of a worklist. The dependency order is structural calculus,
traces, worklist comparison, finite-proof consistency, then the explicit
cosheaf model. The final section states the limitations and next example.
The preceding supplement is preserved and used for its typed fold theorem.

| Location | Issue or editorial risk | Implemented treatment |
| --- | --- | --- |
| Abstract | Conditions were too compressed | Explicit product-compatible ranges, finite limits, extensivity, weak choice, stable length coverage |
| §1 | Modern restriction notation could be mistaken for Heller's exact definition | Typed seven-map semigroup structure and separate explanations of Heller's and Lengyel's iteration definitions |
| §2 | “Range image” could conceal a regularity assumption | Definition of regularity followed by graph pullback and kernel-pair descent proofs |
| §§2–3 | Covers were used before their composite behavior was explained | Explicit finite-join and cover-composition paragraphs |
| §4 | Tree height and computation length could be conflated | Separate height and size covers and explicit cofinal bounds |
| §5 | Atom positions could be confused with atom values | Fixed shape, finite required-equality relation, then categorical equality chain |
| §5 | Logical negation versus inverse image | Explicitly distinguished next to the constructors |
| §6 | “Cosheaf” could leave variance and products ambiguous | Covariant open-set functor, coequalizer property, arrow-category equivalence, computational morphisms |
| §6 | Splitting antecedent was ambiguous | Named R_→ as the category being split |
| §7 | A small example could invite an excessive general claim | Nontrivial-cover product obstruction and exact next construction stated |

## Definitions and typography

Composition, domains, split objects, total category, ranges, weak choice,
and agreement unions precede their proofs. Each functor's source, target,
object action, and morphism action are stated. Parameter ranges are explicit.
The partial slice and the polynomial on domain spans are introduced before
the worklist theorem. The cosheaf/arrow equivalence includes the inverse
object assignment and natural transformations.

The two diagrams use TikZ and have typed arrows. Displayed formulas are
punctuated as parts of sentences. The source makes no Kelly-enrichment
claim. Review process remarks occur in this directory, not in the paper.

## Verification and scope

Compilation of the exact final source succeeded without warnings,
undefined references, or overfull/underfull boxes. All 14 rendered pages
were inspected. No clipping, collisions, or broken diagrams were found.
Reference numbers into the unchanged supplement were checked against its
source order; the incorrect errata subsection reference was repaired.

The prior 23-page manuscript and older Lean files were not subjected to
a new full writing review. The existing verification is reused for
unchanged sources. This review does not certify the mathematics or novelty.
