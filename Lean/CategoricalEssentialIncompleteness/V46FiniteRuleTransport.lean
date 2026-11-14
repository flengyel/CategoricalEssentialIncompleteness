/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Inference
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Finite premise tuples and rule objects under finite-limit preservation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FiniteRuleTransport

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] (G : C ⥤ D) [PreservesFiniteLimits G]

def powerIso (X : C) : (n : ℕ) → G.obj (finitePower X n) ≅ finitePower (G.obj X) n
  | 0 => asIso (terminalComparison G)
  | 1 => Iso.refl _
  | n + 2 => asIso (prodComparison G (finitePower X (n + 1)) X) ≪≫
      prod.mapIso (powerIso X (n + 1)) (Iso.refl _)

theorem power_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    G.map (finitePowerMap f n) ≫ (powerIso G Y n).hom =
      (powerIso G X n).hom ≫ finitePowerMap (G.map f) n := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero => simp [powerIso, finitePowerMap]
    | succ n =>
      change G.map (prod.map (finitePowerMap f (n + 1)) f) ≫
          (prodComparison G _ _ ≫ prod.map (powerIso G Y (n + 1)).hom (𝟙 _)) =
        (prodComparison G _ _ ≫ prod.map (powerIso G X (n + 1)).hom (𝟙 _)) ≫
          prod.map (finitePowerMap (G.map f) (n + 1)) (G.map f)
      rw [← Category.assoc, prodComparison_natural, Category.assoc, prod.map_map, ih]
      simp only [Category.assoc, prod.map_map, Category.id_comp, Category.comp_id]

@[simp] theorem powerIso_one (X : C) : (powerIso G X 1).hom = 𝟙 _ := rfl

@[simp] theorem powerIso_two (X : C) :
    (powerIso G X 2).hom = prodComparison G X X := by
  simp [powerIso, finitePower]

variable {F : C} {N : ℕ} (R : RulePresentation F N)

def mappedRules : RulePresentation (G.obj F) N where
  instances i := G.obj (R.instances i)
  premises i := G.map (R.premises i) ≫ (powerIso G F i.val).hom
  conclusion i := G.map (R.conclusion i)

def ruleObjectIso (Q : Over F) (i : Fin (N + 1)) :
    G.obj (R.ruleObject Q i) ≅ (mappedRules G R).ruleObject ((Over.post G).obj Q) i :=
  PreservesPullback.iso G (R.premises i) (finitePowerMap Q.hom i.val) ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 _) (powerIso G Q.left i.val).hom
      (powerIso G F i.val).hom (by simp [mappedRules])
      (power_naturality G Q.hom i.val))

theorem ruleObjectIso_fst (Q : Over F) (i : Fin (N + 1)) :
    (ruleObjectIso G R Q i).hom ≫ pullback.fst _ _ = G.map (pullback.fst _ _) := by
  simp [ruleObjectIso]

theorem ruleObjectIso_snd (Q : Over F) (i : Fin (N + 1)) :
    (ruleObjectIso G R Q i).hom ≫ pullback.snd _ _ =
      G.map (pullback.snd _ _) ≫ (powerIso G Q.left i.val).hom := by
  simp [ruleObjectIso]

theorem ruleObjectIso_conclusion (Q : Over F) (i : Fin (N + 1)) :
    (ruleObjectIso G R Q i).hom ≫ (mappedRules G R).ruleConclusion ((Over.post G).obj Q) i =
      G.map (R.ruleConclusion Q i) := by
  change _ ≫ (pullback.fst _ _ ≫ G.map (R.conclusion i)) = _
  rw [← Category.assoc, ruleObjectIso_fst, ← G.map_comp]
  rfl

end CategoricalEssentialIncompleteness.V46.FiniteRuleTransport
