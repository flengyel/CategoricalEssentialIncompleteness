/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46CategoricalListOperations
import Mathlib.CategoryTheory.RegularCategory.Basic

/-! # Morphisms of constant parameter families -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D]

@[simp] theorem parameterPair_eta {X A B : D} (f : X ⟶ A ⨯ B) :
    prod.lift (f ≫ prod.fst) (f ≫ prod.snd) = f := by
  apply prod.hom_ext <;> simp

/-- A map of constant families determined by its value coordinate. -/
def parameterHom {P X Y : D} (f : P ⨯ X ⟶ Y) :
    constantFamily P X ⟶ constantFamily P Y :=
  Over.homMk (prod.lift prod.fst f) (by simp [constantFamily])

@[simp] theorem parameterHom_value {P X Y : D} (f : P ⨯ X ⟶ Y) :
    (parameterHom f).left ≫ prod.snd = f := by simp [parameterHom]

theorem parameterHom_eta {P X Y : D}
    (f : constantFamily P X ⟶ constantFamily P Y) :
    parameterHom (f.left ≫ prod.snd) = f := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (prod.lift_fst _ _).trans (Over.w f).symm
  · simp [parameterHom]

/-- The variable and recursive-value maps into a product of families. -/
def parameterStep (P V W : D) :
    constantFamily P (V ⨯ W) ⟶ constantFamily P V ⨯ constantFamily P W :=
  prod.lift (parameterHom (prod.snd ≫ prod.fst))
    (parameterHom (prod.snd ≫ prod.snd))

@[simp] theorem parameterStep_head (P V W : D) :
    (parameterStep P V W).left ≫ listStepHead P V W =
      (prod.snd : P ⨯ (V ⨯ W) ⟶ V ⨯ W) ≫ prod.fst := by
  change (parameterStep P V W).left ≫
    (prod.fst : constantFamily P V ⨯ constantFamily P W ⟶ _).left ≫ prod.snd = _
  rw [← Category.assoc, ← Over.comp_left]
  rw [parameterStep, prod.lift_fst]
  exact parameterHom_value _

@[simp] theorem parameterStep_value (P V W : D) :
    (parameterStep P V W).left ≫ listStepValue P V W =
      (prod.snd : P ⨯ (V ⨯ W) ⟶ V ⨯ W) ≫ prod.snd := by
  change (parameterStep P V W).left ≫
    (prod.snd : constantFamily P V ⨯ constantFamily P W ⟶ _).left ≫ prod.snd = _
  rw [← Category.assoc, ← Over.comp_left]
  rw [parameterStep, prod.lift_snd]
  exact parameterHom_value _

@[simp] theorem parameterStep_base (P V W : D) :
    (parameterStep P V W).left ≫
      (constantFamily P V ⨯ constantFamily P W).hom = prod.fst :=
  Over.w _

@[simp] theorem constantProductComparison_head (P V W : D) :
    constantProductComparison P V W ≫
      parameterHom (prod.snd ≫ prod.fst : P ⨯ (V ⨯ W) ⟶ V) = prod.fst := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp only [Over.comp_left, constantProductComparison, parameterHom,
      Over.homMk_left, Category.assoc, prod.lift_fst]
    exact (Over.w (prod.fst : constantFamily P V ⨯ constantFamily P W ⟶ _)).symm
  · simp [constantProductComparison, parameterHom]

@[simp] theorem constantProductComparison_value (P V W : D) :
    constantProductComparison P V W ≫
      parameterHom (prod.snd ≫ prod.snd : P ⨯ (V ⨯ W) ⟶ W) = prod.snd := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp only [Over.comp_left, constantProductComparison, parameterHom,
      Over.homMk_left, Category.assoc, prod.lift_fst]
    exact (Over.w (prod.snd : constantFamily P V ⨯ constantFamily P W ⟶ _)).symm
  · simp [constantProductComparison, parameterHom]

/-- Products of constant families have their canonical product comparison. -/
def parameterStepIso (P V W : D) :
    constantFamily P (V ⨯ W) ≅ constantFamily P V ⨯ constantFamily P W where
  hom := parameterStep P V W
  inv := constantProductComparison P V W
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · have h := Over.w (parameterStep P V W ≫ constantProductComparison P V W)
      change (parameterStep P V W ≫ constantProductComparison P V W).left ≫
        prod.fst = prod.fst at h
      simpa only [Over.id_left, Category.id_comp] using h
    · simp only [Over.comp_left, Over.id_left, Category.id_comp,
        constantProductComparison, Over.homMk_left, Category.assoc, prod.lift_snd]
      change (parameterStep P V W).left ≫
        prod.lift (listStepHead P V W) (listStepValue P V W) = prod.snd
      rw [prod.comp_lift, parameterStep_head, parameterStep_value]
      apply prod.hom_ext <;> simp
  inv_hom_id := by
    apply prod.hom_ext
    · simp [parameterStep]
    · simp [parameterStep]

instance parameterStep_isIso (P V W : D) : IsIso (parameterStep P V W) :=
  (parameterStepIso P V W).isIso_hom

@[simp, reassoc] theorem parameterStep_comparison (P V W : D) :
    parameterStep P V W ≫ constantProductComparison P V W =
      𝟙 (constantFamily P (V ⨯ W)) :=
  (parameterStepIso P V W).hom_inv_id

@[simp] theorem parameterStep_map_head {P V W X : D}
    (f : constantFamily P W ⟶ constantFamily P X) :
    (parameterStep P V W ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫
      listStepHead P V X = (prod.snd : P ⨯ (V ⨯ W) ⟶ _) ≫ prod.fst := by
  calc
    _ = ((parameterStep P V W ≫ prod.map (𝟙 (constantFamily P V)) f) ≫
        (prod.fst : constantFamily P V ⨯ constantFamily P X ⟶ _)).left ≫ prod.snd :=
      (Category.assoc _ _ _).symm
    _ = (parameterStep P V W ≫
        (prod.fst : constantFamily P V ⨯ constantFamily P W ⟶ _)).left ≫ prod.snd := by
      rw [Category.assoc, prod.map_fst, Category.comp_id]
    _ = _ := by
      simpa only [Over.comp_left, Category.assoc, listStepHead] using parameterStep_head P V W

@[simp] theorem parameterStep_map_value {P V W X : D}
    (f : constantFamily P W ⟶ constantFamily P X) :
    (parameterStep P V W ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫
      listStepValue P V X =
      prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f.left ≫ prod.snd := by
  calc
    _ = ((parameterStep P V W ≫ prod.map (𝟙 (constantFamily P V)) f) ≫
        (prod.snd : constantFamily P V ⨯ constantFamily P X ⟶ _)).left ≫ prod.snd :=
      (Category.assoc _ _ _).symm
    _ = ((parameterStep P V W ≫
        (prod.snd : constantFamily P V ⨯ constantFamily P W ⟶ _)) ≫ f).left ≫ prod.snd := by
      rw [Category.assoc, prod.map_snd, ← Category.assoc]
    _ = _ := by
      rw [parameterStep, prod.lift_snd]
      simp only [parameterHom, Over.homMk_left, Over.comp_left, Category.assoc]

theorem parameterStep_natural {P X Y X' Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (constantFamilyFunctor P).map (prod.map f g) ≫ parameterStep P X' Y' =
      parameterStep P X Y ≫
        prod.map ((constantFamilyFunctor P).map f) ((constantFamilyFunctor P).map g) := by
  apply prod.hom_ext
  · simp only [Category.assoc, parameterStep, prod.lift_fst]
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [constantFamilyFunctor, parameterHom, Over.comp_left, Category.assoc]
  · simp only [Category.assoc, parameterStep, prod.lift_snd]
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [constantFamilyFunctor, parameterHom, Over.comp_left, Category.assoc]

theorem constantProductComparison_natural {P X Y X' Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    prod.map ((constantFamilyFunctor P).map f) ((constantFamilyFunctor P).map g) ≫
        constantProductComparison P X' Y' =
      constantProductComparison P X Y ≫ (constantFamilyFunctor P).map (prod.map f g) := by
  have h := parameterStep_natural (P := P) f g
  dsimp only [constantFamilyFunctor] at h ⊢
  apply (cancel_epi (parameterStep P X Y)).mp
  rw [← Category.assoc, ← h, Category.assoc, parameterStep_comparison]
  simp only [Category.comp_id, parameterStep_comparison_assoc]

theorem constantCoproductComparison_natural [HasFiniteCoproducts D]
    {P X Y X' Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    coprod.map ((constantFamilyFunctor P).map f) ((constantFamilyFunctor P).map g) ≫
        constantCoproductComparison P X' Y' =
      constantCoproductComparison P X Y ≫ (constantFamilyFunctor P).map (coprod.map f g) := by
  exact (coprodComparison_natural (constantFamilyFunctor P) f g).symm

end CategoricalEssentialIncompleteness.V46
