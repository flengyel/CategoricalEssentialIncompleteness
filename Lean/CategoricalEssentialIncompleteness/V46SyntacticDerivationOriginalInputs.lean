/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInputPullback
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationEncoderIsos

/-! Arithmetic sources of the original inference endofunctor summands. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {F Q : PredicateCategory T} {N : ℕ}
variable (R : RulePresentation F N) (q : GraphMorphism T Q F) (i : Fin (N + 1))

theorem encodedPremises_arrow :
    representedArrow T (encodedPremises T R i) =
      R.premises i ≫ representedArrow T (finitePowerEncoder T F i.val) := by
  change representedArrow T (chosenGraph T (R.premises i)) ≫
    representedArrow T (finitePowerEncoder T F i.val) = _
  rw [chosenGraph_class]

/-- The child projection is transported back to the original chosen finite power. -/
def originalChildren : @Quiver.Hom (PredicateCategory T) inferInstance
    (ruleInputCarrier R q i) (finitePower (D := PredicateCategory T) Q i.val) :=
  representedArrow T (ruleInputChildren R q i) ≫ (finitePowerIso T Q i.val).inv

theorem original_square :
    representedArrow T (ruleInputLabel R q i) ≫ R.premises i =
      originalChildren R q i ≫ finitePowerMap (representedArrow T q) i.val := by
  apply (cancel_mono (finitePowerIso T F i.val).hom).mp
  simp only [originalChildren, Category.assoc, finitePowerIso_hom,
    tupleMorphism_compatibility]
  rw [← encodedPremises_arrow, ruleInput_square]
  simp only [← finitePowerIso_hom, Iso.inv_hom_id_assoc]

/-- Transport of the proved literal matching pullback gives the inference pullback, with
each child over its own premise conclusion. -/
theorem original_isPullback :
    IsPullback (representedArrow T (ruleInputLabel R q i)) (originalChildren R q i)
      (R.premises i) (finitePowerMap (representedArrow T q) i.val) := by
  have hp : IsPullback (representedArrow T (ruleInputLabel R q i))
      (representedArrow T (ruleInputChildren R q i))
      (representedArrow T (encodedPremises T R i))
      (representedArrow T (tupleMorphism q i.val)) :=
    RuleInput.isPullback (encodedPremises T R i) (tupleMorphism q i.val)
  refine IsPullback.mk' (original_square R q i) ?_ ?_
  · intro X u v hu hv
    apply hp.hom_ext hu
    have hh := congrArg (fun f => f ≫ (finitePowerIso T Q i.val).hom) hv
    simpa only [originalChildren, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh
  · intro X a b hab
    have hraw : a ≫ representedArrow T (encodedPremises T R i) =
        (b ≫ (finitePowerIso T Q i.val).hom) ≫ representedArrow T (tupleMorphism q i.val) := by
      rw [encodedPremises_arrow, ← Category.assoc, hab, Category.assoc,
        tupleMorphism_compatibility]
      simp only [Category.assoc, finitePowerIso_hom]
    obtain ⟨u, hu, hv⟩ := hp.exists_lift a (b ≫ (finitePowerIso T Q i.val).hom) hraw
    refine ⟨u, hu, ?_⟩
    change u ≫ representedArrow T (ruleInputChildren R q i) ≫
      (finitePowerIso T Q i.val).inv = b
    rw [← Category.assoc, hv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism is over the conclusion object F. -/
def ruleInputIso : CategoryTheory.Iso (C := PredicateCategory T)
    (ruleInputCarrier R q i) (R.ruleObject (Over.mk (representedArrow T q)) i) :=
  (original_isPullback R q i).isoPullback

@[simp, reassoc] theorem ruleInputIso_label :
    (ruleInputIso R q i).hom ≫ pullback.fst _ _ =
      representedArrow T (ruleInputLabel R q i) :=
  (original_isPullback R q i).isoPullback_hom_fst

@[simp, reassoc] theorem ruleInputIso_conclusion :
    (ruleInputIso R q i).hom ≫ R.ruleConclusion (Over.mk (representedArrow T q)) i =
      representedArrow T (ruleInputConclusion R q i) := by
  rw [RulePresentation.ruleConclusion, ← Category.assoc, ruleInputIso_label]
  change representedArrow T (ruleInputLabel R q i) ≫ R.conclusion i =
    representedArrow T (ruleInputLabel R q i) ≫
      representedArrow T (chosenGraph T (R.conclusion i))
  rw [chosenGraph_class]

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
