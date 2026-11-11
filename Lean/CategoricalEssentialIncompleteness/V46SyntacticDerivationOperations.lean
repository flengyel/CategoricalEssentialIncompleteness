/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOriginalInputs

/-! Positive arithmetic root operations of an actual inference algebra. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {F Q : PredicateCategory T} {N : ℕ}
variable (R : RulePresentation F N) (q : GraphMorphism T Q F)
variable (α : R.inference.obj (Over.mk (representedArrow T q)) ⟶ Over.mk (representedArrow T q))
variable (i : Fin (N + 1))

/-- The supplied algebra is applied only on the proved matching input
pullback, transported into its actual inference summand. -/
def ruleOperationArrow : @Quiver.Hom (PredicateCategory T) inferInstance
    (ruleInputCarrier R q i) Q :=
  (ruleInputIso R q i).hom ≫
    Sigma.ι (R.ruleObject (Over.mk (representedArrow T q))) i ≫ α.left

def ruleOperation : GraphMorphism T (ruleInputCarrier R q i) Q :=
  chosenGraph T (ruleOperationArrow R q α i)

/-- These are derived T-proofs on the positive matching carrier. -/
theorem ruleOperation_total :
    T ⊢ totalSentence (ruleInputCarrier R q i) (ruleOperation R q α i).graph :=
  (ruleOperation R q α i).total

theorem ruleOperation_support :
    T ⊢ supportSentence (ruleInputCarrier R q i) Q (ruleOperation R q α i).graph :=
  (ruleOperation R q α i).support

/-- The actual slice-morphism equation gives the parent conclusion;
individual child conclusions remain the ordered premise tuple. -/
theorem ruleOperation_projection :
    representedArrow T (ruleOperation R q α i) ≫ representedArrow T q =
      representedArrow T (ruleInputConclusion R q i) := by
  rw [ruleOperation, chosenGraph_class]
  have hα : α.left ≫ representedArrow T q =
      Sigma.desc (R.ruleConclusion (Over.mk (representedArrow T q))) := Over.w α
  change ((ruleInputIso R q i).hom ≫
    Sigma.ι (R.ruleObject (Over.mk (representedArrow T q))) i ≫ α.left) ≫
      representedArrow T q = _
  simpa only [Category.assoc, hα, Sigma.ι_comp_desc] using ruleInputIso_conclusion R q i

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
