import CategoricalEssentialIncompleteness.V46SyntacticDerivationOriginalInputs

/-! Literal arithmetic inputs present the original H_R summands over F. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {F Q : PredicateCategory T} {N : ℕ}
variable (R : RulePresentation F N) (q : GraphMorphism T Q F) (i : Fin (N + 1))
example : IsPullback (representedArrow T (ruleInputLabel R q i)) (originalChildren R q i)
    (R.premises i) (finitePowerMap (representedArrow T q) i.val) := original_isPullback R q i
example : CategoryTheory.Iso (C := PredicateCategory T)
    (ruleInputCarrier R q i) (R.ruleObject (Over.mk (representedArrow T q)) i) := ruleInputIso R q i
example : (ruleInputIso R q i).hom ≫ R.ruleConclusion (Over.mk (representedArrow T q)) i =
    representedArrow T (ruleInputConclusion R q i) := ruleInputIso_conclusion R q i
