/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonOptions

/-! # Lifted option constructors for the uniform syntax functor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.Options
open CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]

omit [Regular C] [Regular D] [FinitaryExtensive D] [PreservesFiniteLimits F] in
/-- Finite-geometry functors preserve the source-fiber coproduct cover. The target fibers
do not have to use the same chosen objects. -/
theorem map_sumFibers_hom_ext {W A B : C} (f : W ⟶ A ⨿ B) {Z : D}
    {g h : F.obj W ⟶ Z}
    (h₀ : F.map (pullback.fst f (coprod.inl : A ⟶ A ⨿ B)) ≫ g =
      F.map (pullback.fst f (coprod.inl : A ⟶ A ⨿ B)) ≫ h)
    (h₁ : F.map (pullback.fst f (coprod.inr : B ⟶ A ⨿ B)) ≫ g =
      F.map (pullback.fst f (coprod.inr : B ⟶ A ⨿ B)) ≫ h) : g = h := by
  apply (isColimitOfPreserves F (SumFibers.isColimit f)).hom_ext
  rintro ⟨i⟩
  cases i
  · exact h₀
  · exact h₁

theorem map_coefficient_failure {W V Y Z : C} {V' Y' Z' : D}
    (i : F.obj V ≅ V') (j : F.obj Y ≅ Y') (l : F.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (u : W ⟶ V ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hu : u ≫ prod.snd = a ≫ coprod.inl) :
    (F.map u ≫ F.map (OptionSyntax.coefficient h)) ≫ (optionIso F l).hom =
      (F.map u ≫ (productIso F i (optionIso F j)).hom) ≫ OptionSyntax.coefficient h' := by
  have ht : (F.map u ≫ (productIso F i (optionIso F j)).hom) ≫ prod.snd =
      (F.map a ≫ (asIso (terminalComparison F)).hom) ≫ coprod.inl := by
    rw [mapped_product_snd,hu,map_none]
  rw [← F.map_comp,coefficient_failure h u a hu,map_fail]
  exact (coefficient_failure h' _ _ ht).symm

theorem map_coefficient_success {W V Y Z : C} {V' Y' Z' : D}
    (i : F.obj V ≅ V') (j : F.obj Y ≅ Y') (l : F.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ l.hom = (productIso F i j).hom ≫ h')
    (u : W ⟶ V ⨯ OptionSyntax.obj Y) (y : W ⟶ Y)
    (hu : u ≫ prod.snd = y ≫ coprod.inr) :
    (F.map u ≫ F.map (OptionSyntax.coefficient h)) ≫ (optionIso F l).hom =
      (F.map u ≫ (productIso F i (optionIso F j)).hom) ≫ OptionSyntax.coefficient h' := by
  have ht : (F.map u ≫ (productIso F i (optionIso F j)).hom) ≫ prod.snd =
      (F.map y ≫ j.hom) ≫ coprod.inr := by
    rw [mapped_product_snd,hu,map_some]
  calc
    _ = prod.lift (F.map (u ≫ prod.fst) ≫ i.hom) (F.map y ≫ j.hom) ≫ h' ≫ coprod.inr := by
      rw [← F.map_comp,coefficient_success h u y hu,map_pair_some F i j l h h' hh]
    _ = _ := by
      rw [coefficient_success h' _ _ ht,mapped_product_fst]

/-- Lifting an arbitrary coefficient constructor commutes with the
finite-geometry functor whenever its ordinary constructor square commutes. -/
theorem map_coefficient {V Y Z : C} {V' Y' Z' : D}
    (i : F.obj V ≅ V') (j : F.obj Y ≅ Y') (l : F.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ l.hom = (productIso F i j).hom ≫ h') :
    F.map (OptionSyntax.coefficient h) ≫ (optionIso F l).hom =
      (productIso F i (optionIso F j)).hom ≫ OptionSyntax.coefficient h' := by
  let p : V ⨯ OptionSyntax.obj Y ⟶ OptionSyntax.obj Y := prod.snd
  apply map_sumFibers_hom_ext F p
  · simpa only [Category.assoc] using map_coefficient_failure F i j l h h'
      (pullback.fst p (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y))
      (pullback.snd p (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y))
      (pullback.condition (f := p) (g := (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y)))
  · simpa only [Category.assoc] using map_coefficient_success F i j l h h' hh
      (pullback.fst p (coprod.inr : Y ⟶ OptionSyntax.obj Y))
      (pullback.snd p (coprod.inr : Y ⟶ OptionSyntax.obj Y))
      (pullback.condition (f := p) (g := (coprod.inr : Y ⟶ OptionSyntax.obj Y)))

theorem map_binary_failure_first {W Y Z : C} {Y' Z' : D}
    (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hu : u ≫ prod.fst = a ≫ coprod.inl) :
    (F.map u ≫ F.map (OptionSyntax.binary h)) ≫ (optionIso F j).hom =
      (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ OptionSyntax.binary h' := by
  have ht : (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ prod.fst =
      (F.map a ≫ (asIso (terminalComparison F)).hom) ≫ coprod.inl := by
    rw [mapped_product_fst,hu,map_none]
  rw [← F.map_comp,binary_failure_first h u a hu,map_fail]
  exact (binary_failure_first h' _ _ ht).symm

theorem map_binary_failure_second {W Y Z : C} {Y' Z' : D}
    (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (y : W ⟶ Y) (a : W ⟶ ⊤_ C)
    (hy : u ≫ prod.fst = y ≫ coprod.inr) (ha : u ≫ prod.snd = a ≫ coprod.inl) :
    (F.map u ≫ F.map (OptionSyntax.binary h)) ≫ (optionIso F j).hom =
      (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ OptionSyntax.binary h' := by
  have ht₁ : (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ prod.fst =
      (F.map y ≫ i.hom) ≫ coprod.inr := by
    rw [mapped_product_fst,hy,map_some]
  have ht₂ : (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ prod.snd =
      (F.map a ≫ (asIso (terminalComparison F)).hom) ≫ coprod.inl := by
    rw [mapped_product_snd,ha,map_none]
  rw [← F.map_comp,binary_failure_second h u y a hy ha,map_fail]
  exact (binary_failure_second h' _ _ _ ht₁ ht₂).symm

theorem map_binary_success {W Y Z : C} {Y' Z' : D}
    (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ j.hom = (productIso F i i).hom ≫ h')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (y z : W ⟶ Y)
    (hy : u ≫ prod.fst = y ≫ coprod.inr) (hz : u ≫ prod.snd = z ≫ coprod.inr) :
    (F.map u ≫ F.map (OptionSyntax.binary h)) ≫ (optionIso F j).hom =
      (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ OptionSyntax.binary h' := by
  have ht₁ : (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ prod.fst =
      (F.map y ≫ i.hom) ≫ coprod.inr := by
    rw [mapped_product_fst,hy,map_some]
  have ht₂ : (F.map u ≫ (productIso F (optionIso F i) (optionIso F i)).hom) ≫ prod.snd =
      (F.map z ≫ i.hom) ≫ coprod.inr := by
    rw [mapped_product_snd,hz,map_some]
  calc
    _ = prod.lift (F.map y ≫ i.hom) (F.map z ≫ i.hom) ≫ h' ≫ coprod.inr := by
      rw [← F.map_comp,binary_success h u y z hy hz,map_pair_some F i i j h h' hh]
    _ = _ := (binary_success h' _ _ _ ht₁ ht₂).symm

/-- Both operand failures and the simultaneous success case are transported for the binary
option operation. -/
theorem map_binary {Y Z : C} {Y' Z' : D}
    (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ j.hom = (productIso F i i).hom ≫ h') :
    F.map (OptionSyntax.binary h) ≫ (optionIso F j).hom =
      (productIso F (optionIso F i) (optionIso F i)).hom ≫ OptionSyntax.binary h' := by
  let p : OptionSyntax.obj Y ⨯ OptionSyntax.obj Y ⟶ OptionSyntax.obj Y := prod.fst
  apply map_sumFibers_hom_ext F p
  · simpa only [Category.assoc] using map_binary_failure_first F i j h h'
      (pullback.fst p coprod.inl) (pullback.snd p coprod.inl) pullback.condition
  · let q : pullback p (coprod.inr : Y ⟶ OptionSyntax.obj Y) ⟶ OptionSyntax.obj Y :=
      pullback.fst p (coprod.inr : Y ⟶ OptionSyntax.obj Y) ≫ prod.snd
    apply map_sumFibers_hom_ext F q
    · have hy : (pullback.fst q coprod.inl ≫ pullback.fst p coprod.inr) ≫ prod.fst =
          (pullback.fst q coprod.inl ≫ pullback.snd p coprod.inr) ≫ coprod.inr := by
        rw [Category.assoc,pullback.condition,← Category.assoc]
      have ha : (pullback.fst q coprod.inl ≫ pullback.fst p coprod.inr) ≫ prod.snd =
          pullback.snd q coprod.inl ≫ coprod.inl := by
        rw [Category.assoc]
        exact pullback.condition
      have h := map_binary_failure_second F i j h h'
        (pullback.fst q coprod.inl ≫ pullback.fst p coprod.inr)
        (pullback.fst q coprod.inl ≫ pullback.snd p coprod.inr)
        (pullback.snd q coprod.inl) hy ha
      simpa only [F.map_comp,Category.assoc] using h
    · have hy : (pullback.fst q coprod.inr ≫ pullback.fst p coprod.inr) ≫ prod.fst =
          (pullback.fst q coprod.inr ≫ pullback.snd p coprod.inr) ≫ coprod.inr := by
        rw [Category.assoc,pullback.condition,← Category.assoc]
      have hz : (pullback.fst q coprod.inr ≫ pullback.fst p coprod.inr) ≫ prod.snd =
          pullback.snd q coprod.inr ≫ coprod.inr := by
        rw [Category.assoc]
        exact pullback.condition
      have h := map_binary_success F i j h h' hh
        (pullback.fst q coprod.inr ≫ pullback.fst p coprod.inr)
        (pullback.fst q coprod.inr ≫ pullback.snd p coprod.inr)
        (pullback.snd q coprod.inr) hy hz
      simpa only [F.map_comp,Category.assoc] using h

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.Options
