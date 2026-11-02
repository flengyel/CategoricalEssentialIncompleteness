# Appendix A prose revision

Reviewed the complete Appendix A of *Logical consequence and essential
incompleteness in recursion categories*, version 46. Consulted the supplied
KLR text, especially §1 points 10–13, 16–17 and the discussions in §§4–5:
connected exposition, complementary explanations, important displays, and
definitions near their use. The edits below apply those principles together
with the user's preference for inline math.

## Existing outline and paragraph functions

- **Categorical hypotheses and notation:** source dependencies; regularity and
  coproduct hypotheses; composition and product conventions; Boolean
  copairings and their identities; conditionals; typed expression notation;
  decidable variables and signatures; initiality stable under parameters.
- **Terms, formulas, and free variables:** scholarly comparisons; the syntax
  endofunctor and initial algebra; constructors, induction, and list folds;
  free-variable lists; sentences and derived existential quantification.
- **Admissible substitution:** structural-recursion dependency; the lifted
  operations and parameterized algebra; quantifier fold; substitution and
  admissibility pullback; binding equation; identity and absent-variable
  substitution, with the simultaneous induction argument.
- **Inference rules and deductively closed subobjects:** inductive-closure
  dependency; the slice endofunctor; closed subobjects; transfer of the initial
  algebra to its regular image and proof of leastness.
- **First-order theories:** cited logical schemes and their parameter objects;
  the rule presentation; generated formula and sentence theories; restriction
  splitting, ranges, and the regular-image lemma; representation of the
  constructed sentence theory and preservation of its range splitting.
- **Propositional theories:** the corresponding syntax and inference
  construction, including positive and negative atomic axioms.

Each remaining paragraph has a definition, construction, proof, source
comparison, dependency, or explanatory function. No reordering was needed.

## Implemented edits

- Removed the recap that powers denote finite products, the repeated
  uniqueness assertion in the substitution proposition, the repeated
  sentencehood restriction after the axiom subobject, and short proof recaps.
- Combined the factorization-system attribution and the range-preservation
  explanation with the constructions they explain.
- Moved short unnumbered assignments, morphism types, and equalities inline,
  including negation, the coproduct decomposition, the variable substitution
  pair, substitution morphisms, identity substitution, rule morphisms, and
  the short range equations.
- Preserved all numbered formulas, diagrams, Boolean copairing equations,
  constructor and free-variable equations, quantifier/admissibility detail,
  hypotheses, types, citation keys and locators, and the named-variable
  terminology. The appendix remains purely categorical.

## Checks and remaining scope

Reread the complete revised appendix continuously. Checked environment and
math-delimiter balance and scanned for editorial-process material and
numerical/incompleteness content; none was found. No new mathematical issue
was identified in this prose pass. Citation claims were preserved, not
independently reverified. Compilation and rendered-page inspection are left
to the combined manuscript build.
