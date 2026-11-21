/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonOptionConstructors


/-! # Lifted option constructors for the uniform syntax functor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
example {V Y Z : C} {V' Y' Z' : D}
    (i : F.obj V ≅ V') (j : F.obj Y ≅ Y') (k : F.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ k.hom=(Options.productIso F i j).hom ≫ h') :
    F.map (OptionSyntax.coefficient h) ≫ (Options.optionIso F k).hom=
      (Options.productIso F i (Options.optionIso F j)).hom ≫ OptionSyntax.coefficient h' :=
  Options.map_coefficient F i j k h h' hh
example {Y Z : C} {Y' Z' : D} (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z')
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ j.hom=(Options.productIso F i i).hom ≫ h') :
    F.map (OptionSyntax.binary h) ≫ (Options.optionIso F j).hom=
      (Options.productIso F (Options.optionIso F i) (Options.optionIso F i)).hom ≫
        OptionSyntax.binary h' := Options.map_binary F i j h h' hh


-- The source-fiber cover includes every option input.
omit [Regular C] [Regular D] in
example {W A B : C} (p : W ⟶ A ⨿ B) {Z : D} {u v : F.obj W ⟶ Z}
    (h₀ : F.map (pullback.fst p (coprod.inl : A ⟶ A ⨿ B)) ≫ u =
      F.map (pullback.fst p (coprod.inl : A ⟶ A ⨿ B)) ≫ v)
    (h₁ : F.map (pullback.fst p (coprod.inr : B ⟶ A ⨿ B)) ≫ u =
      F.map (pullback.fst p (coprod.inr : B ⟶ A ⨿ B)) ≫ v) : u = v :=
  Options.map_sumFibers_hom_ext F p h₀ h₁

-- Failure does not require the successful constructor square.
example {W V Y Z : C} {V' Y' Z' : D}
    (i : F.obj V ≅ V') (j : F.obj Y ≅ Y') (k : F.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (u : W ⟶ V ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hu : u ≫ prod.snd = a ≫ (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y)) :
    (F.map u ≫ F.map (OptionSyntax.coefficient h)) ≫ (Options.optionIso F k).hom =
      (F.map u ≫ (Options.productIso F i (Options.optionIso F j)).hom) ≫
        OptionSyntax.coefficient h' :=
  Options.map_coefficient_failure F i j k h h' u a hu
example {W V Y Z : C} {V' Y' Z' : D}
    (i : F.obj V ≅ V') (j : F.obj Y ≅ Y') (k : F.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ k.hom = (Options.productIso F i j).hom ≫ h')
    (u : W ⟶ V ⨯ OptionSyntax.obj Y) (y : W ⟶ Y)
    (hu : u ≫ prod.snd = y ≫ (coprod.inr : Y ⟶ OptionSyntax.obj Y)) :
    (F.map u ≫ F.map (OptionSyntax.coefficient h)) ≫ (Options.optionIso F k).hom =
      (F.map u ≫ (Options.productIso F i (Options.optionIso F j)).hom) ≫
        OptionSyntax.coefficient h' :=
  Options.map_coefficient_success F i j k h h' hh u y hu

-- The first failure and success-then-failure cases retain operand order.
example {W Y Z : C} {Y' Z' : D}
    (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z')
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hu : u ≫ prod.fst = a ≫ (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y)) :
    (F.map u ≫ F.map (OptionSyntax.binary h)) ≫ (Options.optionIso F j).hom =
      (F.map u ≫ (Options.productIso F (Options.optionIso F i) (Options.optionIso F i)).hom) ≫
        OptionSyntax.binary h' :=
  Options.map_binary_failure_first F i j h h' u a hu
example {W Y Z : C} {Y' Z' : D}
    (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z')
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (y : W ⟶ Y) (a : W ⟶ ⊤_ C)
    (hy : u ≫ prod.fst = y ≫ (coprod.inr : Y ⟶ OptionSyntax.obj Y))
    (ha : u ≫ prod.snd = a ≫ (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y)) :
    (F.map u ≫ F.map (OptionSyntax.binary h)) ≫ (Options.optionIso F j).hom =
      (F.map u ≫ (Options.productIso F (Options.optionIso F i) (Options.optionIso F i)).hom) ≫
        OptionSyntax.binary h' :=
  Options.map_binary_failure_second F i j h h' u y a hy ha
example {W Y Z : C} {Y' Z' : D}
    (i : F.obj Y ≅ Y') (j : F.obj Z ≅ Z')
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ j.hom = (Options.productIso F i i).hom ≫ h')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (y z : W ⟶ Y)
    (hy : u ≫ prod.fst = y ≫ (coprod.inr : Y ⟶ OptionSyntax.obj Y))
    (hz : u ≫ prod.snd = z ≫ (coprod.inr : Y ⟶ OptionSyntax.obj Y)) :
    (F.map u ≫ F.map (OptionSyntax.binary h)) ≫ (Options.optionIso F j).hom =
      (F.map u ≫ (Options.productIso F (Options.optionIso F i) (Options.optionIso F i)).hom) ≫
        OptionSyntax.binary h' :=
  Options.map_binary_success F i j h h' hh u y z hy hz
