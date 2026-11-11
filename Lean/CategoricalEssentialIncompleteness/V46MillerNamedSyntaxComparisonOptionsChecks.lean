/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonOptions


/-! # Statement checks in `V46MillerNamedSyntaxComparisonOptionsChecks` -/

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
variable {W X Y : C} {X' Y' : D} (i : F.obj X ≅ X') (j : F.obj Y ≅ Y')
example : F.map (coprod.inr : X ⟶ OptionSyntax.obj X) ≫ (Options.optionIso F i).hom=
    i.hom ≫ coprod.inr := Options.optionIso_inr F i
example : F.map (OptionSyntax.fail : W ⟶ OptionSyntax.obj X) ≫ (Options.optionIso F i).hom=
    (OptionSyntax.fail : F.obj W ⟶ OptionSyntax.obj X') := Options.map_fail F i
example (f : X ⟶ Y) (g : X' ⟶ Y') (h : F.map f ≫ j.hom=i.hom ≫ g) :
    F.map (OptionSyntax.map f) ≫ (Options.optionIso F j).hom=
      (Options.optionIso F i).hom ≫ OptionSyntax.map g := Options.map_option_map F i j f g h

example : F.obj (OptionSyntax.obj X) ≅ OptionSyntax.obj X' := Options.optionIso F i
example : F.obj (X ⨯ Y) ≅ X' ⨯ Y' := Options.productIso F i j
example : F.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X) ≫ (Options.optionIso F i).hom=
    (asIso (terminalComparison F)).hom ≫ coprod.inl := Options.optionIso_inl F i
example : (Options.productIso F i j).hom ≫ (prod.fst : X' ⨯ Y' ⟶ X')=
    F.map (prod.fst : X ⨯ Y ⟶ X) ≫ i.hom := Options.productIso_fst F i j
example : (Options.productIso F i j).hom ≫ (prod.snd : X' ⨯ Y' ⟶ Y')=
    F.map (prod.snd : X ⨯ Y ⟶ Y) ≫ j.hom := Options.productIso_snd F i j
example (k : W ⟶ X ⨯ Y) : (F.map k ≫ (Options.productIso F i j).hom) ≫ prod.fst=
    F.map (k ≫ prod.fst) ≫ i.hom := Options.mapped_product_fst F i j k
example (k : W ⟶ X ⨯ Y) : (F.map k ≫ (Options.productIso F i j).hom) ≫ prod.snd=
    F.map (k ≫ prod.snd) ≫ j.hom := Options.mapped_product_snd F i j k
example (x : W ⟶ X) (y : W ⟶ Y) :
    F.map (prod.lift x y) ≫ (Options.productIso F i j).hom=
      prod.lift (F.map x ≫ i.hom) (F.map y ≫ j.hom) := Options.map_lift F i j x y
example (x : W ⟶ X) :
    F.map (x ≫ (coprod.inr : X ⟶ OptionSyntax.obj X)) ≫ (Options.optionIso F i).hom=
      (F.map x ≫ i.hom) ≫ coprod.inr := Options.map_some F i x
example (x : W ⟶ ⊤_ C) :
    F.map (x ≫ (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X)) ≫ (Options.optionIso F i).hom=
      (F.map x ≫ (asIso (terminalComparison F)).hom) ≫ coprod.inl := Options.map_none F i x
example {Z : C} {Z' : D} (k : F.obj Z ≅ Z') (h : X ⨯ Y ⟶ Z) (h' : X' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ k.hom=(Options.productIso F i j).hom ≫ h') (x : W ⟶ X) (y : W ⟶ Y) :
    F.map (prod.lift x y ≫ h ≫ (coprod.inr : Z ⟶ OptionSyntax.obj Z)) ≫
        (Options.optionIso F k).hom=
      prod.lift (F.map x ≫ i.hom) (F.map y ≫ j.hom) ≫ h' ≫ coprod.inr :=
  Options.map_pair_some F i j k h h' hh x y
