/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxParameterFamily


/-! # Statement checks in `V46MillerNamedSyntaxParameterFamilyChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterTransport
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
  (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F] (R : C)

example : PreservesFiniteCoproducts (ListTransport.sliceFunctor F R) := inferInstance

example : terminalComparison (ListTransport.sliceFunctor F R) ≫ constantUnitComparison (F.obj R) =
    (ListTransport.sliceFunctor F R).map (constantUnitComparison R) ≫
      (ListTransport.familyComparison F R (⊤_ C)).hom ≫
        (constantFamilyFunctor (F.obj R)).map (terminalComparison F) := family_unit F R

example (X Y : C) :
    prodComparison (ListTransport.sliceFunctor F R) (constantFamily R X) (constantFamily R Y) ≫
      prod.map (ListTransport.familyComparison F R X).hom (ListTransport.familyComparison F R Y).hom ≫
        constantProductComparison (F.obj R) (F.obj X) (F.obj Y) =
      (ListTransport.sliceFunctor F R).map (constantProductComparison R X Y) ≫
        (ListTransport.familyComparison F R (X ⨯ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (prodComparison F X Y) := family_product F R X Y

example (X Y : C) :
    inv (coprodComparison (ListTransport.sliceFunctor F R) (constantFamily R X) (constantFamily R Y)) ≫
      coprod.map (ListTransport.familyComparison F R X).hom (ListTransport.familyComparison F R Y).hom ≫
        constantCoproductComparison (F.obj R) (F.obj X) (F.obj Y) =
      (ListTransport.sliceFunctor F R).map (constantCoproductComparison R X Y) ≫
        (ListTransport.familyComparison F R (X ⨿ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (inv (coprodComparison F X Y)) := family_sum F R X Y

example {X Y : C} {X' Y' : D} (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    prodComparison (ListTransport.sliceFunctor F R) (constantFamily R X) (constantFamily R Y) ≫
      prod.map ((ListTransport.familyComparison F R X).hom ≫ (constantFamilyFunctor (F.obj R)).map u)
        ((ListTransport.familyComparison F R Y).hom ≫ (constantFamilyFunctor (F.obj R)).map v) ≫
          constantProductComparison (F.obj R) X' Y' =
      (ListTransport.sliceFunctor F R).map (constantProductComparison R X Y) ≫
        (ListTransport.familyComparison F R (X ⨯ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (prodComparison F X Y ≫ prod.map u v) :=
  family_product_map F R u v

example {X Y : C} {X' Y' : D} (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    inv (coprodComparison (ListTransport.sliceFunctor F R) (constantFamily R X) (constantFamily R Y)) ≫
      coprod.map ((ListTransport.familyComparison F R X).hom ≫ (constantFamilyFunctor (F.obj R)).map u)
        ((ListTransport.familyComparison F R Y).hom ≫ (constantFamilyFunctor (F.obj R)).map v) ≫
          constantCoproductComparison (F.obj R) X' Y' =
      (ListTransport.sliceFunctor F R).map (constantCoproductComparison R X Y) ≫
        (ListTransport.familyComparison F R (X ⨿ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (inv (coprodComparison F X Y) ≫ coprod.map u v) :=
  family_sum_map F R u v

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterTransport
