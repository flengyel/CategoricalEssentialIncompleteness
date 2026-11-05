import CategoricalEssentialIncompleteness.V46SyntacticDerivationOperations

/-! Exact typed root operations of an arbitrary supplied inference algebra. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {F Q : PredicateCategory T} {N : ℕ}
  (R : RulePresentation F N) (q : GraphMorphism T Q F)
  (α : R.inference.obj (Over.mk (representedArrow T q)) ⟶ Over.mk (representedArrow T q))
  (i : Fin (N + 1))
example : GraphMorphism T (ruleInputCarrier R q i) Q := ruleOperation R q α i
example : representedArrow T (ruleOperation R q α i) ≫ representedArrow T q =
    representedArrow T (ruleInputConclusion R q i) := ruleOperation_projection R q α i
