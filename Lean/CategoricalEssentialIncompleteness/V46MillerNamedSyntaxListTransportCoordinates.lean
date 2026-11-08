/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransport
import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportBooleans
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
open Derivation
variable {C D : Type} [Category C] [Category D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]

omit [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
theorem map_lift {X A B : C} (f : X ⟶ A) (g : X ⟶ B) :
    F.map (prod.lift f g) ≫ prodComparison F A B=prod.lift (F.map f) (F.map g) := by
  apply prod.hom_ext
  · simp only [Category.assoc,prodComparison_fst,← F.map_comp,prod.lift_fst]
  · simp only [Category.assoc,prodComparison_snd,← F.map_comp,prod.lift_snd]

variable (U X Y : C) (X' Y' : D) (i : F.obj X ≅ X') (j : F.obj Y ≅ Y')
def listStepComparison :
    (sliceFunctor F U).obj (constantFamily U X ⨯ constantFamily U Y) ≅
      constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y' :=
  asIso (prodComparison (sliceFunctor F U) (constantFamily U X) (constantFamily U Y)) ≪≫
    prod.mapIso (coefficientComparison F U X X' i) (coefficientComparison F U Y Y' j)

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
  [PreservesFiniteLimits F] [PreservesFiniteCoproducts F] in
private theorem slice_map_left {A B : Over U} (f : A ⟶ B) :
    ((sliceFunctor F U).map f).left = F.map f.left := rfl

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
theorem listStepComparison_parameter :
    (listStepComparison F U X Y X' Y' i j).hom.left ≫
      (constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y').hom =
      F.map (constantFamily U X ⨯ constantFamily U Y).hom := by
  exact Over.w (listStepComparison F U X Y X' Y' i j).hom

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
private theorem listStepComparison_fst :
    (listStepComparison F U X Y X' Y' i j).hom ≫
      (prod.fst : constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y' ⟶ constantFamily (F.obj U) X') =
    (sliceFunctor F U).map
      (prod.fst : constantFamily U X ⨯ constantFamily U Y ⟶ constantFamily U X) ≫
      (coefficientComparison F U X X' i).hom := by
  change (prodComparison (sliceFunctor F U) (constantFamily U X) (constantFamily U Y) ≫
    prod.map (coefficientComparison F U X X' i).hom (coefficientComparison F U Y Y' j).hom) ≫
      prod.fst = _
  simp only [Category.assoc,prod.map_fst,prodComparison_fst_assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
private theorem listStepComparison_snd :
    (listStepComparison F U X Y X' Y' i j).hom ≫
      (prod.snd : constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y' ⟶ constantFamily (F.obj U) Y') =
    (sliceFunctor F U).map
      (prod.snd : constantFamily U X ⨯ constantFamily U Y ⟶ constantFamily U Y) ≫
      (coefficientComparison F U Y Y' j).hom := by
  change (prodComparison (sliceFunctor F U) (constantFamily U X) (constantFamily U Y) ≫
    prod.map (coefficientComparison F U X X' i).hom (coefficientComparison F U Y Y' j).hom) ≫
      prod.snd = _
  simp only [Category.assoc,prod.map_snd,prodComparison_snd_assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
theorem listStepComparison_head :
    (listStepComparison F U X Y X' Y' i j).hom.left ≫ listStepHead (F.obj U) X' Y' =
      F.map (listStepHead U X Y) ≫ i.hom := by
  have hp : (listStepComparison F U X Y X' Y' i j).hom.left ≫
      (prod.fst : constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y' ⟶ constantFamily (F.obj U) X').left =
      F.map (prod.fst : constantFamily U X ⨯ constantFamily U Y ⟶ constantFamily U X).left ≫
        (coefficientComparison F U X X' i).hom.left := by
    simpa only [Over.comp_left,slice_map_left] using congrArg Over.Hom.left
      (listStepComparison_fst F U X Y X' Y' i j)
  calc
    _ = ((listStepComparison F U X Y X' Y' i j).hom.left ≫
        (prod.fst : constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y' ⟶ constantFamily (F.obj U) X').left) ≫
          prod.snd := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ prod.snd) hp
    _ = F.map (prod.fst : constantFamily U X ⨯ constantFamily U Y ⟶ constantFamily U X).left ≫
        (F.map (prod.snd : U ⨯ X ⟶ X) ≫ i.hom) := by
      rw [Category.assoc,coefficientComparison_snd]
    _ = _ := by simp only [listStepHead,constantFamily,Functor.map_comp,Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
theorem listStepComparison_value :
    (listStepComparison F U X Y X' Y' i j).hom.left ≫ listStepValue (F.obj U) X' Y' =
      F.map (listStepValue U X Y) ≫ j.hom := by
  have hp : (listStepComparison F U X Y X' Y' i j).hom.left ≫
      (prod.snd : constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y' ⟶ constantFamily (F.obj U) Y').left =
      F.map (prod.snd : constantFamily U X ⨯ constantFamily U Y ⟶ constantFamily U Y).left ≫
        (coefficientComparison F U Y Y' j).hom.left := by
    simpa only [Over.comp_left,slice_map_left] using congrArg Over.Hom.left
      (listStepComparison_snd F U X Y X' Y' i j)
  calc
    _ = ((listStepComparison F U X Y X' Y' i j).hom.left ≫
        (prod.snd : constantFamily (F.obj U) X' ⨯ constantFamily (F.obj U) Y' ⟶ constantFamily (F.obj U) Y').left) ≫
          prod.snd := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ prod.snd) hp
    _ = F.map (prod.snd : constantFamily U X ⨯ constantFamily U Y ⟶ constantFamily U Y).left ≫
        (F.map (prod.snd : U ⨯ Y ⟶ Y) ≫ j.hom) := by
      rw [Category.assoc,coefficientComparison_snd]
    _ = _ := by simp only [listStepValue,constantFamily,Functor.map_comp,Category.assoc]


/-- The parameter and the cons head use the same literal variable map. -/
theorem listStepComparison_test {V Y : C} {Y' : D} (j : F.obj Y ≅ Y')
    (S : DecidableVariables V) :
    (listStepComparison F V V Y (F.obj V) Y' (Iso.refl _) j).hom.left ≫
      (prod.lift (constantFamily (F.obj V) (F.obj V) ⨯ constantFamily (F.obj V) Y').hom
        (listStepHead (F.obj V) (F.obj V) Y') ≫ (Derivation.mappedEquality F S).test)=
      F.map (prod.lift (constantFamily V V ⨯ constantFamily V Y).hom
        (listStepHead V V Y) ≫ S.test) ≫ (Derivation.booleanIso F).hom := by
  let k := listStepComparison F V V Y (F.obj V) Y' (Iso.refl _) j
  let a := prod.lift (constantFamily V V ⨯ constantFamily V Y).hom (listStepHead V V Y)
  let a' := prod.lift (constantFamily (F.obj V) (F.obj V) ⨯ constantFamily (F.obj V) Y').hom
    (listStepHead (F.obj V) (F.obj V) Y')
  have h : k.hom.left ≫ a'=F.map a ≫ prodComparison F V V := by
    change k.hom.left ≫ prod.lift _ _=_
    rw [prod.comp_lift,listStepComparison_parameter,listStepComparison_head]
    simp only [Iso.refl_hom,Category.comp_id]
    exact (map_lift F _ _).symm
  change k.hom.left ≫ (a' ≫ (Derivation.mappedEquality F S).test)=F.map (a ≫ S.test) ≫ _
  rw [← Category.assoc,h,Category.assoc,← map_decidable_test F S,
    ← Category.assoc,← F.map_comp]
end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
