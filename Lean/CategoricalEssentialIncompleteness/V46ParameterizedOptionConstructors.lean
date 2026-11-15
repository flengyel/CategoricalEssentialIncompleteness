/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedOption

/-! # Parameter-dependent values of Option constructors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ParameterizedOption
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P W Y Y' Z Z' : D}

/-- A computation equation on arbitrary parameterized inputs suffices. -/
theorem map_natural_value (f : P ⨯ Y ⟶ Z) (g : P ⨯ Y' ⟶ Z')
    (h : Y ⟶ Y') (j : Z ⟶ Z')
    (hw : ∀ {A : D} (p : A ⟶ P) (y : A ⟶ Y),
      prod.lift p (y ≫ h) ≫ g = prod.lift p y ≫ f ≫ j)
    (p : W ⟶ P) (a : W ⟶ OptionSyntax.obj Y) :
    map g p (a ≫ OptionSyntax.map h) = map f p a ≫ OptionSyntax.map j := by
  apply map_natural f g h j _ p a
  have hm : prod.map (𝟙 P) h = prod.lift prod.fst (prod.snd ≫ h) := by
    apply prod.hom_ext <;> simp
  simpa only [hm, prod.lift_fst_snd, Category.id_comp] using
    hw (prod.fst : P ⨯ Y ⟶ P) prod.snd

theorem map_binary_ok (f : P ⨯ Y ⟶ Z) (g : P ⨯ Y' ⟶ Z')
    (h : Y ⨯ Y ⟶ Y') (j : Z ⨯ Z ⟶ Z')
    (hw : ∀ {A : D} (p : A ⟶ P) (y z : A ⟶ Y),
      prod.lift p (prod.lift y z ≫ h) ≫ g =
        prod.lift (prod.lift p y ≫ f) (prod.lift p z ≫ f) ≫ j)
    (p : W ⟶ P) (y : W ⟶ Y) (b : W ⟶ OptionSyntax.obj Y) :
    map g p (prod.lift (y ≫ coprod.inr) b ≫ OptionSyntax.binary h) =
      prod.lift (prod.lift p y ≫ f ≫ coprod.inr) (map f p b) ≫ OptionSyntax.binary j := by
  apply OptionSyntax.hom_ext b
  · let i := pullback.fst b coprod.inl
    have hb : i ≫ b = OptionSyntax.fail := OptionSyntax.fiber_fail b
    have hin : i ≫ (prod.lift (y ≫ coprod.inr) b ≫ OptionSyntax.binary h) =
        OptionSyntax.fail := by
      simpa only [prod.comp_lift_assoc, hb, Category.assoc] using
        OptionSyntax.binary_ok_fail h (i ≫ y)
    rw [comp_map_fail g p _ i hin, prod.comp_lift_assoc, comp_map_fail f p b i hb]
    simp only [← Category.assoc, OptionSyntax.binary_ok_fail]
  · let i := pullback.fst b coprod.inr
    let z := pullback.snd b coprod.inr
    have hb : i ≫ b = z ≫ coprod.inr := pullback.condition
    have hin : i ≫ (prod.lift (y ≫ coprod.inr) b ≫ OptionSyntax.binary h) =
        (prod.lift (i ≫ y) z ≫ h) ≫ coprod.inr := by
      simpa only [prod.comp_lift_assoc, hb, Category.assoc] using
        OptionSyntax.binary_ok h (i ≫ y) z
    rw [comp_map_ok g p _ i _ hin, prod.comp_lift_assoc, comp_map_ok f p b i z hb]
    simp only [← Category.assoc, OptionSyntax.binary_ok]
    simpa only [Category.assoc, prod.comp_lift_assoc] using
      congrArg (fun k => k ≫ coprod.inr) (hw (i ≫ p) (i ≫ y) z)

theorem map_binary (f : P ⨯ Y ⟶ Z) (g : P ⨯ Y' ⟶ Z')
    (h : Y ⨯ Y ⟶ Y') (j : Z ⨯ Z ⟶ Z')
    (hw : ∀ {A : D} (p : A ⟶ P) (y z : A ⟶ Y),
      prod.lift p (prod.lift y z ≫ h) ≫ g =
        prod.lift (prod.lift p y ≫ f) (prod.lift p z ≫ f) ≫ j)
    (p : W ⟶ P) (a b : W ⟶ OptionSyntax.obj Y) :
    map g p (prod.lift a b ≫ OptionSyntax.binary h) =
      prod.lift (map f p a) (map f p b) ≫ OptionSyntax.binary j := by
  apply OptionSyntax.hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = OptionSyntax.fail := OptionSyntax.fiber_fail a
    have hin : i ≫ (prod.lift a b ≫ OptionSyntax.binary h) = OptionSyntax.fail := by
      simp only [prod.comp_lift_assoc, ha, OptionSyntax.binary_fail_left]
    rw [comp_map_fail g p _ i hin, prod.comp_lift_assoc, comp_map_fail f p a i ha,
      OptionSyntax.binary_fail_left]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    dsimp only [i] at ha
    rw [map_precomp]
    simp only [prod.comp_lift_assoc, ha]
    rw [map_binary_ok f g h j hw, comp_map_ok f p a i y ha]
    simp only [map_precomp, i]

/-- A constructor that ignores its coefficient at the value level keeps
exactly the original Option value. -/
theorem map_ignore_coefficient {V : D} (f : P ⨯ Y ⟶ Z) (g : P ⨯ Y' ⟶ Z)
    (h : V ⨯ Y ⟶ Y')
    (hw : ∀ {A : D} (p : A ⟶ P) (v : A ⟶ V) (y : A ⟶ Y),
      prod.lift p (prod.lift v y ≫ h) ≫ g = prod.lift p y ≫ f)
    (p : W ⟶ P) (v : W ⟶ V) (a : W ⟶ OptionSyntax.obj Y) :
    map g p (prod.lift v a ≫ OptionSyntax.coefficient h) = map f p a := by
  apply OptionSyntax.hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = OptionSyntax.fail := OptionSyntax.fiber_fail a
    have hin : i ≫ (prod.lift v a ≫ OptionSyntax.coefficient h) = OptionSyntax.fail := by
      simp only [prod.comp_lift_assoc, ha, OptionSyntax.coefficient_fail]
    rw [comp_map_fail g p _ i hin, comp_map_fail f p a i ha]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    have hin : i ≫ (prod.lift v a ≫ OptionSyntax.coefficient h) =
        (prod.lift (i ≫ v) y ≫ h) ≫ coprod.inr := by
      simp only [prod.comp_lift_assoc, ha, Category.assoc, OptionSyntax.coefficient_ok]
    rw [comp_map_ok g p _ i _ hin, comp_map_ok f p a i y ha]
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ coprod.inr) (hw (i ≫ p) (i ≫ v) y)

/-- A coefficient constructor changes the payload but preserves the
success/failure test used by a mask. -/
theorem mask_coefficient {V A B C : D} (h : V ⨯ A ⟶ B) (v : W ⟶ V)
    (a : W ⟶ OptionSyntax.obj A) (w : W ⟶ C) :
    OptionSyntax.mask w (prod.lift v a ≫ OptionSyntax.coefficient h) =
      OptionSyntax.mask w a := by
  apply OptionSyntax.hom_ext a
  · let i := pullback.fst a coprod.inl
    have ha : i ≫ a = OptionSyntax.fail := OptionSyntax.fiber_fail a
    have hin : i ≫ (prod.lift v a ≫ OptionSyntax.coefficient h) = OptionSyntax.fail := by
      simp only [prod.comp_lift_assoc, ha, OptionSyntax.coefficient_fail]
    rw [OptionSyntax.comp_mask_fail _ _ i hin, OptionSyntax.comp_mask_fail _ _ i ha]
  · let i := pullback.fst a coprod.inr
    let y := pullback.snd a coprod.inr
    have ha : i ≫ a = y ≫ coprod.inr := pullback.condition
    have hin : i ≫ (prod.lift v a ≫ OptionSyntax.coefficient h) =
        (prod.lift (i ≫ v) y ≫ h) ≫ coprod.inr := by
      simp only [prod.comp_lift_assoc, ha, Category.assoc, OptionSyntax.coefficient_ok]
    rw [OptionSyntax.comp_mask_ok _ _ i _ hin, OptionSyntax.comp_mask_ok _ _ i y ha]

end CategoricalEssentialIncompleteness.V46.ParameterizedOption
