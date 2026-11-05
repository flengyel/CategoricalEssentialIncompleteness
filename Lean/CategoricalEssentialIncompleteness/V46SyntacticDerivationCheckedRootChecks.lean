import CategoricalEssentialIncompleteness.V46SyntacticDerivationCheckedRoot

/-! The success source is exactly the original, independently typed premise pullback. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.CheckedRoot
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
  {F Z : D} {N : ℕ} (R : RulePresentation F N) (Q : Over F) (i : Fin (N + 1))
  (E : DecidableVariables (finitePower F i.val)) (h : R.ruleObject Q i ⟶ Z)
example : R.ruleObject Q i = pullback (R.premises i) (finitePowerMap Q.hom i.val) := rfl
example : IsPullback (matchingMap R Q i) h (operation R Q i E h) coprod.inr :=
  operation_isPullback R Q i E h
example : matchingMap R Q i ≫ operation R Q i E h = h ≫ coprod.inr := operation_matching R Q i E h
