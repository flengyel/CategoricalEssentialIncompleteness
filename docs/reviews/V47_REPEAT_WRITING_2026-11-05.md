# CEI v47: second mathematical-writing review

The second review found one misplaced family of definitions, repeated preliminary material, an ambiguous antecedent, and two locally undeclared uses of notation or terminology. The repairs preserve the mathematical statements and shorten the exposition. The nine-file editorial patch removes 116 words before the two final integration corrections recorded below.

## Text and source consulted

Reviewed the assembled v47 manuscript in `cei-editorial-nov5/manuscript/latex`: abstract, introduction, categorical preliminaries, comparison and internal-theory sections, syntactic construction, interpretation and soundness, arithmetic and numerical applications, Miller sequences, the three-point construction, and Appendices A–D. The fresh reading was shared with two readers: one read the syntactic construction and Appendix A; the other read interpretation, arithmetic, and numerical realization. The remaining sections and appendices were read by this reviewer. The previous review reports were not used as certificates of the revised text.

The governing writing source was Knuth, Larrabee, and Roberts, [*Mathematical Writing*](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf), particularly §1 on connected exposition and notation, §4 on the placement of definitions, and §5 on introducing symbols near their use. The requested Došen–Petrić economy determines the treatment of repetition and nonessential modifiers. The source supports those writing principles; the concrete cuts below are editorial judgments about this manuscript.

## Organization

| Manuscript division | Function | Assessment |
|---|---|---|
| Introduction and related work | State the categorical incompleteness problem and locate the contributions | The revised opening identifies the objects, hypotheses, and applications. No further rearrangement is needed. |
| §2 | Supply restriction-category, range, splitting, product, and recursion-category terminology | Place partial-map categories and restriction monomorphisms here, before later applications. |
| §§3–4 | Prove diagonal comparison and derive incompleteness for internal theories | The argument progresses from comparison to semantic consistency to source inseparability. |
| §5 and Appendix A | Construct syntax, substitution, proof objects, and deductive closure | Keep the main construction in §5 and the categorical closure arguments in Appendix A; remove repeated preliminary definitions from the appendix. |
| §6 | Interpret syntax and prove soundness | The code model and the semantic structure are distinguished before soundness. |
| §7 and its numerical subsections | Apply the comparison to arithmetic, indexed theories, and numerical realizations | The types and the successive realization maps are supplied before their uses. One pronoun obscured which split object had the stated identity. |
| §8 | Pass from recursive comparison to Miller-indexed constructions | The representation-dependent data are specified where needed. |
| §9 and Appendix B | Construct the cosheaf recursion category, its Turing morphism, and component theories | Keep the construction and application in §9 and its structural proofs in Appendix B. Remove the second introduction of the general partial-map category. |
| Appendices C–D | Give the section-lifting counterexample and distinguish faithful families from completeness tests | The negative mathematical claims are substantive and remain. |

The existing order supports the proofs. No alternative outline is proposed.

## Implemented repairs

All paths below are relative to `cei-editorial-nov5/manuscript/latex`. Stable theorem and section labels identify the passages even if compilation changes page numbers.

| Location | Finding | Implemented change |
|---|---|---|
| `sections/02-categorical-preliminaries.tex`, partial maps and restriction idempotents | `\operatorname{Par}(\mathcal E,\operatorname{Mono})` was used in `prop:interpreted-theory` before its definition in §9. | Defined the objects, span morphisms, isomorphism relation, pullback composition, restrictions, and identification of the total category in §2. Explicitly stated that `Mono` consists of all monomorphisms. Retained the Cockett–Lack citation with the definition. |
| Same subsection | Restriction monomorphisms occurred in the internal-theory section before their Appendix A definition. | Moved the definition to §2: a total `m:A\to X` with partial inverse `r:X\rightharpoonup A`, satisfying `rm=1_A` and `mr=\bar r`. |
| `sections/09-three-point-space.tex`, construction of `\mathcal A` | Repeated the general definition of `Par`, its monic-leg convention, and its span description. | Replaced that introduction by “Put `\mathcal A=\operatorname{Par}(\mathcal E,\operatorname{Mono})`.” Retained the local facts that monomorphisms are componentwise injections and partial morphisms are c.e. subfunctors with natural transformations. |
| `appendices/a-syntax-and-theories.tex`, material preceding `lem:range-regular-image` | Repeated splitting, totality, restriction order, receiving, ranges, the agreement law, and restriction monomorphisms. | Removed the repeated definitions. The original §2 definitions, including the moved restriction-monomorphism definition, supply them before use. |
| Same appendix, paragraph beginning “Since `\mathcal D` is regular” | Reintroduced the general partial-map category before using its regular-image structure. | Kept the consequence of regularity and the range citation; removed the repeated span construction. |
| Same appendix, transition after `lem:range-regular-image` | Defined a restriction functor again before applying it to a splitting. | Replaced the repetition by “Let `G:\mathcal S\to\mathcal S'` be a restriction functor preserving ranges. Applying `G` to the splitting in Lemma … gives …”. The equations remain. |
| `sections/05a-internal-syntax.tex`, derivation coding | “A derivation code records its rule labels and ordered children” restated the immediately preceding grammar. | Deleted the sentence. |
| Same file, derivation closure | “The original morphism” added a historical qualifier with no mathematical distinction. | Changed it to “The morphism”. |
| `sections/08-essential-incompleteness-of-arithmetic.tex`, opening construction of `S` and `t_\Gamma` | “its identity” followed a reference to `t_\Gamma` although the identity belonged to the split sentence object. | Wrote “The identity of `S` is `[\operatorname{Sent}]_{\PA}`.” |
| `sections/06-interpretation-in-models.tex`, Boolean interpretation of logical axioms | “the displayed classical propositional” contained an empty positional modifier. | Removed “displayed”; retained “classical”, which specifies the logic. |
| `sections/08c-numerical-realization.tex`, two source carriers | “the two displayed source carriers” contained the same empty modifier. | Changed it to “the two source carriers”. |
| `sections/04-miller-sequences.tex`; `sections/09-three-point-space.tex`; two passages in `appendices/c-section-lifting.tex` | “total inverse images” could attach totality to the inverse-image operation instead of the morphism. | Replaced the four occurrences by “inverse images along total morphisms”. |

The exact nine-file diff is saved as `cei-v47-repeat-writing.patch` beside this report.

## Final integration corrections

The complete final reread of §9 and Appendix B produced two additional local corrections, sent to the integrating editor after the nine-file patch was declared final:

1. In the proof of `thm:cosheaf-observation`, change “preserved by total inverse image” to “preserved by inverse images along total morphisms”. The integrating editor confirmed applying this correction.
2. In the proof of `prop:fork-recursion`, the symbol `m^\dagger` had no local declaration. Replace “provides a restriction monomorphism `m:Z\to V`” by “provides a restriction monomorphism `m:Z\to V` with partial inverse `m^\dagger:V\rightharpoonup Z`”. The integrating editor confirmed this correction for the final build.

These corrections clarify terminology and typing without changing a hypothesis or proof step.

## Definition and terminology audit

The general partial-map category and restriction monomorphism are now defined in §2 before all their later uses. The two category constructions in §9 can therefore specialize existing notation directly. The local declarations in §9 specify the indexing category, numerical carriers, subfunctors, the universal object, sequence encodings, frame, and evaluation functors before their formulas are used. Appendix B introduces the acceptable numbering and its specialization property before constructing the Turing morphism. The added declaration of `m^\dagger` supplies the one remaining local partial-inverse symbol.

“Morphism” and “Turing morphism” retain their mathematical senses. “Total,” “standard,” “ordinary,” “canonical,” “exactly,” and “precisely” were retained where they distinguish morphism domains, external natural numbers, oracle computation, a specified construction, equality of domains, or an equivalence. Conditions concerning arbitrary slice objects, induction internal to a model, domain equality, and the original bound-variable body carry proof content and were retained. The revised application sections contain no repeated warnings about formalization status or review procedure.

Two optional compressions were considered and left unchanged. The explicit finite-coproduct verification of the Boolean identities in Appendix A remains useful proof detail. “In children-before-parent order” in numerical proof evaluation already states the required traversal order; replacing it by “from leaves to root” would be a synonym change.

## Validation and resulting scope

The nine-file patch was compared with the captured pre-edit v47 sources. Every label is unchanged. No numbered theorem, lemma, proposition, or definition was removed; no hypothesis, conclusion, quantifier, or labeled display was altered. The omitted agreement-law display repeated the definition already supplied in §2. The two integration corrections add no new mathematical assumption.

This pass produced no new mathematical counterexample or theorem repair. Its findings are definition placement, local typing, repetition, and sentence economy. Citation correctness is recorded in the separate primary-source citation audit; this pass moved the Cockett–Lack citation with its definition and retained the application-specific citations. Compilation, visual inspection of the final PDF, and the exact-source Lean checks are performed by the integrating editor after all v47 corrections are assembled.
