/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityOptions

/-! # Naturality of the option-valued constructor operations -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.OptionSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

@[simp, reassoc] theorem fail_map {W Y Z : D} (f : Y ⟶ Z) :
    (fail : W ⟶ obj Y) ≫ map f = fail := by
  simp [fail, map]

theorem hom_ext {W Y Z : D} (a : W ⟶ obj Y) {g h : W ⟶ Z}
    (h₀ : pullback.fst a coprod.inl ≫ g = pullback.fst a coprod.inl ≫ h)
    (h₁ : pullback.fst a coprod.inr ≫ g = pullback.fst a coprod.inr ≫ h) : g = h :=
  BinaryCofan.IsColimit.hom_ext (SumFibers.isColimit a) h₀ h₁

@[reassoc] theorem binary_fail_left {W Y Z : D} (h : Y ⨯ Y ⟶ Z) (z : W ⟶ obj Y) :
    prod.lift fail z ≫ binary h = fail := by
  let k : W ⟶ obj Y ⨯ obj Y := prod.lift fail z
  have hk : k ≫ prod.fst = terminal.from W ≫ coprod.inl := by simp [k, fail]
  change k ≫ binary h = _
  unfold binary
  rw [SumFibers.comp_caseOf_inl _ _ _ k (terminal.from W) hk]
  simp [fail]

@[reassoc] theorem binary_ok_fail {W Y Z : D} (h : Y ⨯ Y ⟶ Z) (y : W ⟶ Y) :
    prod.lift (y ≫ coprod.inr) fail ≫ binary h = fail := by
  let k : W ⟶ obj Y ⨯ obj Y := prod.lift (y ≫ coprod.inr) fail
  have hk : k ≫ prod.fst = y ≫ coprod.inr := by simp [k]
  let a := pullback.lift k y hk
  have ha : a ≫
      (pullback.fst (prod.fst : obj Y ⨯ obj Y ⟶ obj Y) coprod.inr ≫ prod.snd) =
      terminal.from W ≫ coprod.inl := by simp [a, k, fail]
  change k ≫ binary h = _
  unfold binary
  rw [SumFibers.comp_caseOf_inr _ _ _ k y hk,
    SumFibers.comp_caseOf_inl _ _ _ a (terminal.from W) ha]
  simp [fail]

@[reassoc] theorem coefficient_fail {W V Y Z : D} (h : V ⨯ Y ⟶ Z) (v : W ⟶ V) :
    prod.lift v fail ≫ coefficient h = fail := by
  let k : W ⟶ V ⨯ obj Y := prod.lift v fail
  have hk : k ≫ prod.snd = terminal.from W ≫ coprod.inl := by simp [k, fail]
  change k ≫ coefficient h = _
  unfold coefficient
  rw [SumFibers.comp_caseOf_inl _ _ _ k (terminal.from W) hk]
  simp [fail]

attribute [reassoc] coefficient_ok binary_ok

theorem fiber_fail {W Y : D} (a : W ⟶ obj Y) :
    pullback.fst a coprod.inl ≫ a = fail := by
  have h : pullback.fst a coprod.inl ≫ a = pullback.snd a coprod.inl ≫ coprod.inl :=
    pullback.condition
  have ht : pullback.snd a coprod.inl = terminal.from _ := Subsingleton.elim _ _
  rw [ht] at h
  exact h

theorem coefficient_natural_value {W V Y Y' Z Z' : D}
    (h : V ⨯ Y ⟶ Z) (h' : V ⨯ Y' ⟶ Z') (p : Y ⟶ Y') (q : Z ⟶ Z')
    (hw : h ≫ q = prod.map (𝟙 V) p ≫ h') (v : W ⟶ V) (a : W ⟶ obj Y) :
    prod.lift v a ≫ coefficient h ≫ map q =
      prod.lift v (a ≫ map p) ≫ coefficient h' := by
  have hw' : h ≫ q ≫ (coprod.inr : Z' ⟶ obj Z') =
      prod.map (𝟙 V) p ≫ h' ≫ coprod.inr := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ coprod.inr) hw
  apply hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = fail := fiber_fail a
    have hap : i ≫ (a ≫ map p) = fail := by rw [← Category.assoc, ha, fail_map]
    dsimp only [i] at ha hap
    simp only [prod.comp_lift_assoc, ha, hap, coefficient_fail_assoc, coefficient_fail,
      fail_map]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    have hap : i ≫ (a ≫ map p) = (y ≫ p) ≫ coprod.inr := by
      rw [← Category.assoc, ha, Category.assoc, map_ok, ← Category.assoc]
    dsimp only [i, y] at ha hap
    simp only [prod.comp_lift_assoc, ha, hap, coefficient_ok_assoc, coefficient_ok,
      map_ok, hw', prod.lift_map_assoc, Category.comp_id]

theorem coefficient_natural {V Y Y' Z Z' : D}
    (h : V ⨯ Y ⟶ Z) (h' : V ⨯ Y' ⟶ Z') (p : Y ⟶ Y') (q : Z ⟶ Z')
    (hw : h ≫ q = prod.map (𝟙 V) p ≫ h') :
    coefficient h ≫ map q = prod.map (𝟙 V) (map p) ≫ coefficient h' := by
  have he : prod.lift (prod.fst : V ⨯ obj Y ⟶ V) (prod.snd ≫ map p) =
      prod.map (𝟙 V) (map p) := by apply prod.hom_ext <;> simp
  simpa only [prod.lift_fst_snd, Category.id_comp, he] using
    coefficient_natural_value h h' p q hw prod.fst prod.snd

theorem binary_ok_natural_value {W Y Y' Z Z' : D}
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z') (p : Y ⟶ Y') (q : Z ⟶ Z')
    (hw : h ≫ q = prod.map p p ≫ h') (y : W ⟶ Y) (b : W ⟶ obj Y) :
    prod.lift (y ≫ coprod.inr) b ≫ binary h ≫ map q =
      prod.lift ((y ≫ p) ≫ coprod.inr) (b ≫ map p) ≫ binary h' := by
  have hw' : h ≫ q ≫ (coprod.inr : Z' ⟶ obj Z') =
      prod.map p p ≫ h' ≫ coprod.inr := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ coprod.inr) hw
  apply hom_ext b
  · let i := pullback.fst b coprod.inl
    have hb : i ≫ b = fail := fiber_fail b
    have hbp : i ≫ (b ≫ map p) = fail := by rw [← Category.assoc, hb, fail_map]
    have hy : i ≫ (y ≫ (coprod.inr : Y ⟶ obj Y)) = (i ≫ y) ≫ coprod.inr := by
      simp only [Category.assoc]
    have hyp : i ≫ ((y ≫ p) ≫ (coprod.inr : Y' ⟶ obj Y')) = ((i ≫ y) ≫ p) ≫ coprod.inr := by
      simp only [Category.assoc]
    dsimp only [i] at hb hbp hy hyp
    simp only [prod.comp_lift_assoc, hb, hbp, hy, hyp,
      binary_ok_fail_assoc, binary_ok_fail, fail_map]
  · let i := pullback.fst b coprod.inr
    let z := pullback.snd b coprod.inr
    have hb : i ≫ b = z ≫ coprod.inr := pullback.condition
    have hbp : i ≫ (b ≫ map p) = (z ≫ p) ≫ coprod.inr := by
      rw [← Category.assoc, hb, Category.assoc, map_ok, ← Category.assoc]
    have hy : i ≫ (y ≫ (coprod.inr : Y ⟶ obj Y)) = (i ≫ y) ≫ coprod.inr := by
      simp only [Category.assoc]
    have hyp : i ≫ ((y ≫ p) ≫ (coprod.inr : Y' ⟶ obj Y')) = ((i ≫ y) ≫ p) ≫ coprod.inr := by
      simp only [Category.assoc]
    dsimp only [i, z] at hb hbp hy hyp
    simp only [prod.comp_lift_assoc, hb, hbp, hy, hyp, binary_ok_assoc, binary_ok,
      map_ok, hw', prod.lift_map_assoc]

theorem binary_natural_value {W Y Y' Z Z' : D}
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z') (p : Y ⟶ Y') (q : Z ⟶ Z')
    (hw : h ≫ q = prod.map p p ≫ h') (a b : W ⟶ obj Y) :
    prod.lift a b ≫ binary h ≫ map q =
      prod.lift (a ≫ map p) (b ≫ map p) ≫ binary h' := by
  apply hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = fail := fiber_fail a
    have hap : i ≫ (a ≫ map p) = fail := by rw [← Category.assoc, ha, fail_map]
    dsimp only [i] at ha hap
    simp only [prod.comp_lift_assoc, ha, hap, binary_fail_left_assoc, binary_fail_left, fail_map]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    have hap : i ≫ (a ≫ map p) = (y ≫ p) ≫ coprod.inr := by
      rw [← Category.assoc, ha, Category.assoc, map_ok, ← Category.assoc]
    have hval := binary_ok_natural_value h h' p q hw y (i ≫ b)
    dsimp only [i, y] at ha hap hval
    simpa only [prod.comp_lift_assoc, ha, hap, Category.assoc] using hval

theorem binary_natural {Y Y' Z Z' : D}
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z') (p : Y ⟶ Y') (q : Z ⟶ Z')
    (hw : h ≫ q = prod.map p p ≫ h') :
    binary h ≫ map q = prod.map (map p) (map p) ≫ binary h' := by
  have he : prod.lift ((prod.fst : obj Y ⨯ obj Y ⟶ obj Y) ≫ map p)
      (prod.snd ≫ map p) = prod.map (map p) (map p) := by
    apply prod.hom_ext <;> simp
  simpa only [prod.lift_fst_snd, Category.id_comp, he] using
    binary_natural_value h h' p q hw prod.fst prod.snd

end CategoricalEssentialIncompleteness.V46.OptionSyntax
