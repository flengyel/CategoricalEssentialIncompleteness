import CategoricalEssentialIncompleteness.V46SyntacticDerivationInputGeometry

/-! The judgement comparison uses the original ordered-premise pullback. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {D : Type u} [Category.{v} D] [Regular D] {F : D} {N : ℕ}
  (R : RulePresentation F N) (Q : Over F) (i : Fin (N + 1))
example : IsPullback (CheckedRoot.matchingMap R Q i) (R.ruleMap (InputGeometry.toJudgement Q) i)
    (prod.map (𝟙 (R.instances i)) (finitePowerMap Q.hom i.val))
    (CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i) := InputGeometry.matching_isPullback R Q i
