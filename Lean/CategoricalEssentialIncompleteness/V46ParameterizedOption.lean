/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46OptionMask

/-! # Option values with a retained internal parameter -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ParameterizedOption
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P W U Y Z : D}

/-- Evaluate a successful option with its parameter; failure remains failure. -/
def map (f : P ⨯ Y ⟶ Z) (p : W ⟶ P) (a : W ⟶ OptionSyntax.obj Y) :
    W ⟶ OptionSyntax.obj Z :=
  SumFibers.caseOf a OptionSyntax.fail
    (prod.lift (pullback.fst a coprod.inr ≫ p) (pullback.snd a coprod.inr) ≫ f ≫ coprod.inr)

@[reassoc] theorem comp_map_fail (f : P ⨯ Y ⟶ Z) (p : W ⟶ P)
    (a : W ⟶ OptionSyntax.obj Y) (k : U ⟶ W) (ha : k ≫ a = OptionSyntax.fail) :
    k ≫ map f p a = OptionSyntax.fail := by
  unfold map
  rw [SumFibers.comp_caseOf_inl _ _ _ k (terminal.from U) ha]
  simp [OptionSyntax.fail]

@[reassoc] theorem comp_map_ok (f : P ⨯ Y ⟶ Z) (p : W ⟶ P)
    (a : W ⟶ OptionSyntax.obj Y) (k : U ⟶ W) (y : U ⟶ Y)
    (ha : k ≫ a = y ≫ coprod.inr) :
    k ≫ map f p a = prod.lift (k ≫ p) y ≫ f ≫ coprod.inr := by
  unfold map
  rw [SumFibers.comp_caseOf_inr _ _ _ k y ha]
  simp only [prod.comp_lift_assoc, pullback.lift_fst_assoc, pullback.lift_snd]

@[simp] theorem map_fail (f : P ⨯ Y ⟶ Z) (p : W ⟶ P) :
    map f p (OptionSyntax.fail : W ⟶ OptionSyntax.obj Y) = OptionSyntax.fail := by
  simpa only [Category.id_comp] using
    comp_map_fail f p (OptionSyntax.fail : W ⟶ OptionSyntax.obj Y) (𝟙 W) (by simp)

@[simp] theorem map_ok (f : P ⨯ Y ⟶ Z) (p : W ⟶ P) (y : W ⟶ Y) :
    map f p (y ≫ (coprod.inr : Y ⟶ OptionSyntax.obj Y)) =
      prod.lift p y ≫ f ≫ coprod.inr := by
  simpa only [Category.id_comp] using comp_map_ok f p (y ≫ coprod.inr) (𝟙 W) y (by simp)

theorem map_precomp (f : P ⨯ Y ⟶ Z) (p : W ⟶ P)
    (a : W ⟶ OptionSyntax.obj Y) (k : U ⟶ W) :
    k ≫ map f p a = map f (k ≫ p) (k ≫ a) := by
  apply OptionSyntax.hom_ext (k ≫ a)
  · let i := pullback.fst (k ≫ a) coprod.inl
    have ha : i ≫ (k ≫ a) = OptionSyntax.fail := OptionSyntax.fiber_fail (k ≫ a)
    have h₁ := comp_map_fail f p a (i ≫ k) (by simpa only [Category.assoc] using ha)
    have h₂ := comp_map_fail f (k ≫ p) (k ≫ a) i ha
    simpa only [Category.assoc] using h₁.trans h₂.symm
  · let i := pullback.fst (k ≫ a) coprod.inr
    let y := pullback.snd (k ≫ a) coprod.inr
    have ha : i ≫ (k ≫ a) = y ≫ coprod.inr := pullback.condition
    have h₁ := comp_map_ok f p a (i ≫ k) y (by simpa only [Category.assoc] using ha)
    have h₂ := comp_map_ok f (k ≫ p) (k ≫ a) i y ha
    simp only [Category.assoc] at h₁ h₂
    exact h₁.trans h₂.symm

/-- Parameterized evaluation also retains the original failure test of a mask. -/
theorem map_mask {A : D} (f : P ⨯ Y ⟶ Z) (p : W ⟶ P)
    (y : W ⟶ Y) (a : W ⟶ OptionSyntax.obj A) :
    map f p (OptionSyntax.mask y a) =
      OptionSyntax.mask (prod.lift p y ≫ f) a := by
  apply OptionSyntax.hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = OptionSyntax.fail := OptionSyntax.fiber_fail a
    rw [map_precomp, OptionSyntax.comp_mask_fail y a i ha, map_fail,
      OptionSyntax.comp_mask_fail _ a i ha]
  · let i := pullback.fst a coprod.inr
    let x := pullback.snd a coprod.inr
    have ha : i ≫ a = x ≫ coprod.inr := pullback.condition
    rw [comp_map_ok f p _ i (i ≫ y)
        (by simpa only [Category.assoc] using OptionSyntax.comp_mask_ok y a i x ha),
      OptionSyntax.comp_mask_ok _ a i x ha]
    simp only [Category.assoc, prod.comp_lift_assoc]

/-- Both branches retain the same parameter, even when it varies on the input. -/
theorem map_branch (f : P ⨯ Y ⟶ Z) (p : W ⟶ P) (b : W ⟶ Two D)
    (a₀ a₁ : W ⟶ OptionSyntax.obj Y) :
    map f p (Two.branch b a₀ a₁) =
      Two.branch b (map f p a₀) (map f p a₁) := by
  apply Two.hom_ext b
  · rw [map_precomp, Two.fiberι_branch, ← map_precomp, Two.fiberι_branch]
    rfl
  · rw [map_precomp, Two.fiberι_branch, ← map_precomp, Two.fiberι_branch]
    rfl

/-- An ordinary result transformation commutes with parameterized evaluation
when its value equation holds on the whole parameter product. -/
theorem map_natural {Y' Z' : D} (f : P ⨯ Y ⟶ Z) (g : P ⨯ Y' ⟶ Z')
    (h : Y ⟶ Y') (j : Z ⟶ Z')
    (hh : prod.map (𝟙 P) h ≫ g = f ≫ j) (p : W ⟶ P)
    (a : W ⟶ OptionSyntax.obj Y) :
    map g p (a ≫ OptionSyntax.map h) = map f p a ≫ OptionSyntax.map j := by
  apply OptionSyntax.hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = OptionSyntax.fail := OptionSyntax.fiber_fail a
    have hap : i ≫ (a ≫ OptionSyntax.map h) = OptionSyntax.fail := by
      rw [← Category.assoc, ha, OptionSyntax.fail_map]
    rw [comp_map_fail g p _ i hap, ← Category.assoc, comp_map_fail f p a i ha,
      OptionSyntax.fail_map]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    have hap : i ≫ (a ≫ OptionSyntax.map h) = (y ≫ h) ≫ coprod.inr := by
      rw [← Category.assoc, ha, Category.assoc, OptionSyntax.map_ok, ← Category.assoc]
    have hm : prod.lift (i ≫ p) (y ≫ h) ≫ g = prod.lift (i ≫ p) y ≫ f ≫ j := by
      simpa only [← Category.assoc, prod.lift_map, Category.comp_id] using
        congrArg (fun k => prod.lift (i ≫ p) y ≫ k) hh
    rw [comp_map_ok g p _ i (y ≫ h) hap, comp_map_ok_assoc f p a i y ha]
    simpa only [Category.assoc, OptionSyntax.map_ok] using
      congrArg (fun k => k ≫ coprod.inr) hm

end CategoricalEssentialIncompleteness.V46.ParameterizedOption
