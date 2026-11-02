# Writing review of version 45 introduction and attribution placement

The revised introduction now introduces the problem, construction, results and literature relationships without reproducing the formal definitions and proof schemas. One compressed sentence needs its reduction hypothesis restored. The attribution changes identify borrowed constructions before their use and preserve the distinction between those constructions and the paper's results.

## Actual outline

The introduction has seven main paragraphs: the Di Paola–Heller objective and three applications; their intrinsic-recursion criterion; the internal theory construction; the two computational criteria; arithmetic; the Miller realization; and the cosheaf realization. A short roadmap follows. The Related work subsection compares categorical foundations and existence theorems; earlier fixed-point/inseparability results; Turing categories and Cockett's incompleteness theorem; Ramesh; and Bauer–Hanson.

This sequence retains the conceptual chain from deduction to generated theories to incompleteness. The removed Split/Tot definitions, formula-object symbols, conclusion-image equation and detailed proof reductions remain in their mathematical sections. Their removal here is relocation of technical work, not a replacement of that work by unexplained abbreviations. The typed range functor remains because its source, target and interpretation role are needed to explain the comparison.

## Required local repair

At “The second criterion starts with an inseparable pair and applies it to the theorem and refutation restriction idempotents of every consistent extension represented in the same category,” the reduction from the pair to a base theory has disappeared. An inseparable pair alone does not give the stated conclusion for arbitrary represented extensions.

Replace those sentences with:

> The second criterion assumes a total reduction of an inseparable pair to the theorem and refutation restriction idempotents of a base theory. The same reduction applies to its consistent represented extensions (Corollary~\ref{cor:domain-incompleteness}).

This restores the necessary premise without reintroducing the proof schema. KLR §1, points 10–13 support connected explanation, and point 17 supports an unambiguous reading; preserving this mathematical premise is an independent correctness requirement, not a special KLR rule.

## Attribution placement

The changed openings in Sections 2, 5 and 8 identify Cockett–Lack terminology, Montagna/Di Paola–Montagna's syntactic categories, and the Miller sequence with Bauer–Hanson's representation formulation before use. Section 6.4 identifies Łoś's theorem as the imported tool while leaving the comparison as the present argument. Section 9 distinguishes Curry's cosheaf definition and the cited partial-map construction from the three-point recursion-category construction. Appendix A.1 identifies the list-recursion dependency, and A.3 compares the structural-recursion device with Gabbay–Pitts without attributing the complete substitution construction to them. The relocated citations do not leave duplicate source explanations at the original positions.

No new undefined symbols are introduced by these changes. The arithmetic model is specified before its functor, and Pfn is named. The earlier distinction between interpreting codes and interpreting decoded formulas survives in prose. The Miller oracle uniformity and the cosheaf same-language extension condition remain explicit. The Ramesh paragraph still states a derivation of Löb, while Bernardi remains a recursion-theoretic antecedent rather than an axiomatized-Löb example.

Scope: the complete version 45 introduction, its difference from the frozen version 44 introduction, and the attribution-placement differences in the six changed source files. KLR §1, particularly points 10–13, 17 and 24, and its discussion of useful referee contributions were consulted from the supplied text. This is a writing/attribution-placement review, not a new primary-source verification, whole-body proof audit, compilation or rendered-layout check. No manuscript files were edited by this agent.

## Resolution

The final source explicitly states the total morphism reducing the fixed inseparable pair to the theorem and refutation restriction idempotents of a base theory, then states its persistence for consistent represented extensions. The required premise is restored without the former proof schema. The roadmap now precedes Related work, keeping that subsection about the literature. The sole finding above is resolved; no further local writing correction is required in the reviewed changes.
