import CategoricalEssentialIncompleteness.V46NamedArithmeticClosedSubstitutionTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedArithmeticClosedSubstitution
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) : 𝗣𝗔 ⊢ closedReplacementSentence V σ π d := closedReplacement_PA V σ π d
