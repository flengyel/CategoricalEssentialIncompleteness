/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxParameterBaseChangeFamily


/-! # Finite-geometry family charts after a base isomorphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterBaseChange
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
  (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
  {R : C} {Q : D} (b : F.obj R ≅ Q)

example : PreservesFiniteLimits (Over.post F ⋙ Over.map b.hom) := inferInstance
example : PreservesFiniteCoproducts (Over.post F ⋙ Over.map b.hom) := inferInstance
example (X : C) : (functor F b).obj (constantFamily R X) ≅ constantFamily Q (F.obj X) :=
  familyComparison F b X
example (X : C) : (familyComparison F b X).hom.left ≫ prod.snd =
    F.map (prod.snd : R ⨯ X ⟶ X) := familyComparison_snd F b X

example (X Y : C) :
    prodComparison (functor F b) (constantFamily R X) (constantFamily R Y) ≫
      prod.map (familyComparison F b X).hom (familyComparison F b Y).hom ≫
        constantProductComparison Q (F.obj X) (F.obj Y) =
      (functor F b).map (constantProductComparison R X Y) ≫
        (familyComparison F b (X ⨯ Y)).hom ≫
          (constantFamilyFunctor Q).map (prodComparison F X Y) := family_product F b X Y

example (X Y : C) :
    inv (coprodComparison (functor F b) (constantFamily R X) (constantFamily R Y)) ≫
      coprod.map (familyComparison F b X).hom (familyComparison F b Y).hom ≫
        constantCoproductComparison Q (F.obj X) (F.obj Y) =
      (functor F b).map (constantCoproductComparison R X Y) ≫
        (familyComparison F b (X ⨿ Y)).hom ≫
          (constantFamilyFunctor Q).map (inv (coprodComparison F X Y)) := family_sum F b X Y

example {X Y : C} {X' Y' : D} (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    prodComparison (functor F b) (constantFamily R X) (constantFamily R Y) ≫
      prod.map ((familyComparison F b X).hom ≫ (constantFamilyFunctor Q).map u)
        ((familyComparison F b Y).hom ≫ (constantFamilyFunctor Q).map v) ≫
          constantProductComparison Q X' Y' =
      (functor F b).map (constantProductComparison R X Y) ≫
        (familyComparison F b (X ⨯ Y)).hom ≫
          (constantFamilyFunctor Q).map (prodComparison F X Y ≫ prod.map u v) :=
  family_product_map F b u v

example {X Y : C} {X' Y' : D} (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    inv (coprodComparison (functor F b) (constantFamily R X) (constantFamily R Y)) ≫
      coprod.map ((familyComparison F b X).hom ≫ (constantFamilyFunctor Q).map u)
        ((familyComparison F b Y).hom ≫ (constantFamilyFunctor Q).map v) ≫
          constantCoproductComparison Q X' Y' =
      (functor F b).map (constantCoproductComparison R X Y) ≫
        (familyComparison F b (X ⨿ Y)).hom ≫
          (constantFamilyFunctor Q).map (inv (coprodComparison F X Y) ≫ coprod.map u v) :=
  family_sum_map F b u v

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterBaseChange
