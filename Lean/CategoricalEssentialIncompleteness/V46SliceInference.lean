/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceRuleObjects
public import CategoricalEssentialIncompleteness.V46AlgebraTransport
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The inference-algebra comparison for an arbitrary parameter slice -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SliceInference
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D] {P : D}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)
local notation "E" => Over.iteratedSliceEquiv F
local notation "G" => Over.forget P

/-- The coefficient comparison uses the constructed relative rule
pullbacks, with their original labels and ordered premises. -/
def carrierBackward (Q : Over F) :
    ((SliceRuleObjects.rules R).inference.obj ((E).functor.obj Q)).left ≅
      ((R.inference.obj Q).left).left :=
  (Sigma.mapIso (fun i => (SliceRuleObjects.iso R Q i).symm)) ≪≫
    asIso (sigmaComparison (G) (R.ruleObject Q))

theorem backward_branch (Q : Over F) (i : Fin (N + 1)) :
    Sigma.ι ((SliceRuleObjects.rules R).ruleObject ((E).functor.obj Q)) i ≫
        (carrierBackward R Q).hom =
      (SliceRuleObjects.iso R Q i).inv ≫ (Sigma.ι (R.ruleObject Q) i).left := by
  simp only [carrierBackward, Iso.trans_hom, Sigma.ι_mapIso_hom_assoc,
    Iso.symm_hom, asIso_hom]
  exact congrArg (fun f => (SliceRuleObjects.iso R Q i).inv ≫ f)
    (ι_comp_sigmaComparison (G) (R.ruleObject Q) i)

def componentBackward (Q : Over F) :
    (SliceRuleObjects.rules R).inference.obj ((E).functor.obj Q) ≅
      (E).functor.obj (R.inference.obj Q) :=
  Over.isoMk (carrierBackward R Q) (by
    change (carrierBackward R Q).hom ≫ (Sigma.desc (R.ruleConclusion Q)).left =
      Sigma.desc ((SliceRuleObjects.rules R).ruleConclusion ((E).functor.obj Q))
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, backward_branch, Category.assoc, Sigma.ι_comp_desc]
    change (SliceRuleObjects.iso R Q i).inv ≫
      (G).map (Sigma.ι (R.ruleObject Q) i) ≫
        (G).map (Sigma.desc (R.ruleConclusion Q)) = _
    rw [← (G).map_comp, Sigma.ι_comp_desc]
    exact SliceRuleObjects.inverse_conclusion R Q i)

theorem forward_branch (Q : Over F) (i : Fin (N + 1)) :
    (Sigma.ι (R.ruleObject Q) i).left ≫ (componentBackward R Q).inv.left =
      (SliceRuleObjects.iso R Q i).hom ≫
        Sigma.ι ((SliceRuleObjects.rules R).ruleObject ((E).functor.obj Q)) i := by
  apply (cancel_mono (componentBackward R Q).hom.left).mp
  have h := congrArg Over.Hom.left (componentBackward R Q).inv_hom_id
  simp only [Over.comp_left, Over.id_left] at h
  erw [Category.assoc, h, Category.comp_id]
  rw [Category.assoc]
  change _ = (SliceRuleObjects.iso R Q i).hom ≫
    (Sigma.ι _ i ≫ (carrierBackward R Q).hom)
  rw [backward_branch, Iso.hom_inv_id_assoc]

theorem component_natural {Q Q' : Over F} (q : Q ⟶ Q') :
    (E).functor.map (R.inference.map q) ≫ (componentBackward R Q').inv =
      (componentBackward R Q).inv ≫
        (SliceRuleObjects.rules R).inference.map ((E).functor.map q) := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (sigmaComparison (G) (R.ruleObject Q))).mp
  apply Sigma.hom_ext
  intro i
  rw [ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison_assoc]
  have h := congrArg Over.Hom.left (Sigma.ι_map (R.ruleMap q) i)
  simp only [Over.comp_left] at h
  change (Sigma.ι (R.ruleObject Q) i).left ≫
      ((Limits.Sigma.map (R.ruleMap q)).left ≫ (componentBackward R Q').inv.left) =
    (Sigma.ι (R.ruleObject Q) i).left ≫ ((componentBackward R Q).inv.left ≫
      Limits.Sigma.map ((SliceRuleObjects.rules R).ruleMap ((E).functor.map q)))
  rw [← Category.assoc, h, Category.assoc, forward_branch,
    ← Category.assoc, SliceRuleObjects.naturality, Category.assoc]
  erw [← Sigma.ι_map]
  erw [← Category.assoc, ← forward_branch]
  exact Category.assoc _ _ _

/-- The iterated-slice equivalence intertwines the complete finite
inference endofunctors, rather than just their evaluations. -/
def comparison : R.inference ⋙ (E).functor ≅
    (E).functor ⋙ (SliceRuleObjects.rules R).inference :=
  NatIso.ofComponents (fun Q => (componentBackward R Q).symm)
    (fun q => component_natural R q)

def algebraEquivalence : Endofunctor.Algebra R.inference ≌
    Endofunctor.Algebra (SliceRuleObjects.rules R).inference :=
  AlgebraTransport.equivalence (E) (comparison R)

/-- Any constructed base deduction algebra yields a deduction algebra
in the slice. The full initiality property is transported back. -/
def algebra (A : Endofunctor.Algebra (SliceRuleObjects.rules R).inference) :
    Endofunctor.Algebra R.inference := (algebraEquivalence R).inverse.obj A

def initial (A : Endofunctor.Algebra (SliceRuleObjects.rules R).inference)
    (hA : IsInitial A) : IsInitial (algebra R A) :=
  IsInitial.isInitialObj (algebraEquivalence R).inverse A hA

end CategoricalEssentialIncompleteness.V46.SliceInference
