/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46OptionSyntaxNaturality

/-! # Replacing the value of an option while preserving failure -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.OptionSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

@[simp, reassoc] theorem comp_fail {U W Y : D} (k : U ⟶ W) :
    k ≫ (fail : W ⟶ obj Y) = fail := by
  simp [fail]

def mask {W Y Z : D} (v : W ⟶ Z) (a : W ⟶ obj Y) : W ⟶ obj Z :=
  SumFibers.caseOf a fail (pullback.fst a coprod.inr ≫ v ≫ coprod.inr)

@[reassoc] theorem comp_mask_fail {U W Y Z : D} (v : W ⟶ Z) (a : W ⟶ obj Y)
    (k : U ⟶ W) (ha : k ≫ a = fail) : k ≫ mask v a = fail := by
  unfold mask
  rw [SumFibers.comp_caseOf_inl _ _ _ k (terminal.from U) ha]
  simp [fail]

@[reassoc] theorem comp_mask_ok {U W Y Z : D} (v : W ⟶ Z) (a : W ⟶ obj Y)
    (k : U ⟶ W) (y : U ⟶ Y) (ha : k ≫ a = y ≫ coprod.inr) :
    k ≫ mask v a = k ≫ v ≫ coprod.inr := by
  unfold mask
  rw [SumFibers.comp_caseOf_inr _ _ _ k y ha]
  simp only [pullback.lift_fst_assoc]

@[simp] theorem mask_fail {W Y Z : D} (v : W ⟶ Z) :
    mask v (fail : W ⟶ obj Y) = fail := by
  simpa only [Category.id_comp] using comp_mask_fail v (fail : W ⟶ obj Y) (𝟙 W) (by simp)

@[simp] theorem mask_ok {W Y Z : D} (v : W ⟶ Z) (y : W ⟶ Y) :
    mask v (y ≫ (coprod.inr : Y ⟶ obj Y)) = v ≫ coprod.inr := by
  simpa only [Category.id_comp] using comp_mask_ok v (y ≫ coprod.inr) (𝟙 W) y (by simp)

theorem mask_precomp {U W Y Z : D} (k : U ⟶ W) (v : W ⟶ Z) (a : W ⟶ obj Y) :
    k ≫ mask v a = mask (k ≫ v) (k ≫ a) := by
  apply hom_ext (k ≫ a)
  · let i := pullback.fst (k ≫ a) coprod.inl
    have ha : i ≫ (k ≫ a) = fail := fiber_fail (k ≫ a)
    have h₁ := comp_mask_fail v a (i ≫ k) (by simpa only [Category.assoc] using ha)
    have h₂ := comp_mask_fail (k ≫ v) (k ≫ a) i ha
    simpa only [Category.assoc] using h₁.trans h₂.symm
  · let i := pullback.fst (k ≫ a) coprod.inr
    let y := pullback.snd (k ≫ a) coprod.inr
    have ha : i ≫ (k ≫ a) = y ≫ coprod.inr := pullback.condition
    have h₁ := comp_mask_ok v a (i ≫ k) y (by simpa only [Category.assoc] using ha)
    have h₂ := comp_mask_ok (k ≫ v) (k ≫ a) i y ha
    simp only [Category.assoc] at h₁ h₂
    exact h₁.trans h₂.symm

theorem mask_map {W Y Y' Z : D} (v : W ⟶ Z) (a : W ⟶ obj Y) (f : Y ⟶ Y') :
    mask v (a ≫ map f) = mask v a := by
  apply hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = fail := fiber_fail a
    have hf : i ≫ (a ≫ map f) = fail := by rw [← Category.assoc, ha, fail_map]
    exact (comp_mask_fail v (a ≫ map f) i hf).trans (comp_mask_fail v a i ha).symm
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    have hf : i ≫ (a ≫ map f) = (y ≫ f) ≫ coprod.inr := by
      rw [← Category.assoc, ha, Category.assoc, map_ok, ← Category.assoc]
    exact (comp_mask_ok v (a ≫ map f) i (y ≫ f) hf).trans (comp_mask_ok v a i y ha).symm

theorem mask_postcomp {W Y Z Z' : D} (v : W ⟶ Z) (a : W ⟶ obj Y) (g : Z ⟶ Z') :
    mask v a ≫ map g = mask (v ≫ g) a := by
  apply hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = fail := fiber_fail a
    calc
      i ≫ (mask v a ≫ map g) = (i ≫ mask v a) ≫ map g := (Category.assoc _ _ _).symm
      _ = fail := by rw [comp_mask_fail v a i ha, fail_map]
      _ = i ≫ mask (v ≫ g) a := (comp_mask_fail (v ≫ g) a i ha).symm
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    calc
      i ≫ (mask v a ≫ map g) = (i ≫ mask v a) ≫ map g := (Category.assoc _ _ _).symm
      _ = (i ≫ v ≫ coprod.inr) ≫ map g :=
        congrArg (fun k => k ≫ map g) (comp_mask_ok v a i y ha)
      _ = i ≫ (v ≫ g) ≫ coprod.inr := by simp only [Category.assoc, map_ok]
      _ = i ≫ mask (v ≫ g) a := (comp_mask_ok (v ≫ g) a i y ha).symm

theorem mask_branch {W Y Z : D} (v : W ⟶ Z) (b : W ⟶ Two D)
    (a₀ a₁ : W ⟶ obj Y) :
    mask v (Two.branch b a₀ a₁) = Two.branch b (mask v a₀) (mask v a₁) := by
  apply Two.hom_ext b
  · rw [mask_precomp, Two.fiberι_branch, ← mask_precomp, Two.fiberι_branch]
    rfl
  · rw [mask_precomp, Two.fiberι_branch, ← mask_precomp, Two.fiberι_branch]
    rfl

theorem mask_coefficient {W V Y Y' Z Z' : D} (h : V ⨯ Y ⟶ Z)
    (h' : V ⨯ Y' ⟶ Z') (v : W ⟶ V) (a : W ⟶ obj Y) (w : W ⟶ Y') :
    mask (prod.lift v w ≫ h') (prod.lift v a ≫ coefficient h) =
      prod.lift v (mask w a) ≫ coefficient h' := by
  apply hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = fail := fiber_fail a
    have hb : i ≫ (prod.lift v a ≫ coefficient h) = fail := by
      simp only [prod.comp_lift_assoc, ha, coefficient_fail]
    rw [comp_mask_fail _ _ i hb, prod.comp_lift_assoc, comp_mask_fail w a i ha,
      coefficient_fail]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    have hb : i ≫ (prod.lift v a ≫ coefficient h) =
        (prod.lift (i ≫ v) y ≫ h) ≫ coprod.inr := by
      simp only [prod.comp_lift_assoc, ha, coefficient_ok, Category.assoc]
    rw [comp_mask_ok _ _ i _ hb, prod.comp_lift_assoc, comp_mask_ok w a i y ha]
    dsimp only [i]
    simp only [← Category.assoc, coefficient_ok]
    rw [prod.comp_lift]

theorem mask_binary_ok {W Y Y' Z Z' : D} (h : Y ⨯ Y ⟶ Z)
    (h' : Y' ⨯ Y' ⟶ Z') (y : W ⟶ Y) (a : W ⟶ obj Y) (v w : W ⟶ Y') :
    mask (prod.lift v w ≫ h') (prod.lift (y ≫ coprod.inr) a ≫ binary h) =
      prod.lift (v ≫ coprod.inr) (mask w a) ≫ binary h' := by
  apply hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = fail := fiber_fail a
    have hb : i ≫ (prod.lift (y ≫ coprod.inr) a ≫ binary h) = fail := by
      rw [prod.comp_lift_assoc, ha]
      simpa only [Category.assoc] using binary_ok_fail h (i ≫ y)
    rw [comp_mask_fail _ _ i hb, prod.comp_lift_assoc, comp_mask_fail w a i ha]
    simpa only [Category.assoc] using (binary_ok_fail h' (i ≫ v)).symm
  · let i := pullback.fst a coprod.inr
    let z := pullback.snd a coprod.inr
    have ha : i ≫ a = z ≫ coprod.inr := pullback.condition
    have hb : i ≫ (prod.lift (y ≫ coprod.inr) a ≫ binary h) =
        (prod.lift (i ≫ y) z ≫ h) ≫ coprod.inr := by
      rw [prod.comp_lift_assoc, ha]
      simpa only [Category.assoc] using binary_ok h (i ≫ y) z
    rw [comp_mask_ok _ _ i _ hb, prod.comp_lift_assoc, comp_mask_ok w a i z ha]
    dsimp only [i]
    simp only [← Category.assoc, binary_ok]
    rw [prod.comp_lift]

theorem mask_binary {W Y Y' Z Z' : D} (h : Y ⨯ Y ⟶ Z)
    (h' : Y' ⨯ Y' ⟶ Z') (a b : W ⟶ obj Y) (v w : W ⟶ Y') :
    mask (prod.lift v w ≫ h') (prod.lift a b ≫ binary h) =
      prod.lift (mask v a) (mask w b) ≫ binary h' := by
  apply hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = fail := fiber_fail a
    have hb : i ≫ (prod.lift a b ≫ binary h) = fail := by
      simp only [prod.comp_lift_assoc, ha, binary_fail_left]
    rw [comp_mask_fail _ _ i hb, prod.comp_lift_assoc, comp_mask_fail v a i ha,
      binary_fail_left]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    dsimp only [i, y] at ha ⊢
    rw [mask_precomp]
    simp only [prod.comp_lift_assoc]
    rw [ha, comp_mask_ok v a i y ha, mask_precomp]
    simpa only [Category.assoc] using mask_binary_ok h h' y (i ≫ b) (i ≫ v) (i ≫ w)

end CategoricalEssentialIncompleteness.V46.OptionSyntax
