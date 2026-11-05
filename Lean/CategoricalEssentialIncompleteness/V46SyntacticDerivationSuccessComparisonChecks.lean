import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessComparison

/-! The constructed success comparison identifies exactly the original inference functor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F : PredicateCategory T} {N : ℕ}
  (R : RulePresentation F N)
example : SliceInitial.functor (PolynomialComparison.ordinary R) (SuccessComparison.validator T R) ⋙
    SuccessComparison.success T ≅ SuccessComparison.success T ⋙ R.inference :=
  SuccessComparison.comparison T R
