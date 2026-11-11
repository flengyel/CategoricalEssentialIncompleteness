/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution

/-! Success equations for the actual option-valued constructors. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.OptionSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

@[simp, reassoc] theorem map_ok {Y Z : D} (f : Y ⟶ Z) :
    coprod.inr ≫ map f = f ≫ coprod.inr := by simp [map]

theorem coefficient_ok {X V Y Z : D} (h : V ⨯ Y ⟶ Z)
    (v : X ⟶ V) (y : X ⟶ Y) :
    prod.lift v (y ≫ coprod.inr) ≫ coefficient h = prod.lift v y ≫ h ≫ coprod.inr := by
  unfold coefficient
  rw [SumFibers.comp_caseOf_inr _ _ _ (prod.lift v (y ≫ coprod.inr)) y (by simp)]
  simp [prod.comp_lift_assoc]

theorem binary_ok {X Y Z : D} (h : Y ⨯ Y ⟶ Z) (y z : X ⟶ Y) :
    prod.lift (y ≫ coprod.inr) (z ≫ coprod.inr) ≫ binary h =
      prod.lift y z ≫ h ≫ coprod.inr := by
  let k : X ⟶ obj Y ⨯ obj Y := prod.lift (y ≫ coprod.inr) (z ≫ coprod.inr)
  have hk : k ≫ prod.fst = y ≫ coprod.inr := by simp [k]
  let a := pullback.lift k y hk
  have ha : a ≫ (pullback.fst (prod.fst : obj Y ⨯ obj Y ⟶ obj Y) coprod.inr ≫
      prod.snd) = z ≫ coprod.inr := by simp [a, k]
  change k ≫ binary h = _
  unfold binary
  rw [SumFibers.comp_caseOf_inr _ _ _ k y hk,
    SumFibers.comp_caseOf_inr _ _ _ a z ha]
  simp [a, k, prod.comp_lift_assoc]

@[simp, reassoc] theorem binary_ok_map {Y Z : D} (h : Y ⨯ Y ⟶ Z) :
    prod.map (coprod.inr : Y ⟶ obj Y) coprod.inr ≫ binary h = h ≫ coprod.inr := by
  simpa using binary_ok h (prod.fst : Y ⨯ Y ⟶ Y) prod.snd

@[simp, reassoc] theorem coefficient_ok_map {V Y Z : D} (h : V ⨯ Y ⟶ Z) :
    prod.map (𝟙 V) (coprod.inr : Y ⟶ obj Y) ≫ coefficient h = h ≫ coprod.inr := by
  have he : prod.map (𝟙 V) (coprod.inr : Y ⟶ obj Y) =
      prod.lift (prod.fst : V ⨯ Y ⟶ V) (prod.snd ≫ coprod.inr) := by
    apply prod.hom_ext <;> simp
  rw [he, coefficient_ok, prod.lift_fst_snd, Category.id_comp]

end CategoricalEssentialIncompleteness.V46.OptionSyntax
