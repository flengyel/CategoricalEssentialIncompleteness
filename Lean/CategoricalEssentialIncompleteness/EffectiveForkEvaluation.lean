/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkTuring
public import CategoricalEssentialIncompleteness.EffectiveForkCoproducts
public import CategoricalEssentialIncompleteness.RangeFunctor

/-! # Component evaluation and endpoint Turing universality -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier)

inductive Component where
  | center | left | right

def evaluation (j : Component) : Object ⥤ Carrier where
  obj X := match j with | .center => X.center | .left => X.left | .right => X.right
  map f := match j with | .center => f.center | .left => f.left | .right => f.right
  map_id X := by cases j <;> rfl
  map_comp f g := by cases j <;> rfl

def evaluationRangeFunctor (j : Component) : RangeFunctor Object Carrier where
  toFunctor := evaluation j
  map_restrict f := by cases j <;> rfl
  map_range f := by cases j <;> rfl
  map_zero X Y := by cases j <;> rfl
  comparison_isIso X Y := by
    cases j
    all_goals
      change IsIso (copair (i0 _ _) (i1 _ _))
      rw [copair_i0_i1]
      infer_instance

theorem evaluation_sup (j : Component) {X : Object} (a b : Idem X) :
    (evaluationRangeFunctor j).mapIdem (a ⊔ b)=
      (evaluationRangeFunctor j).mapIdem a ⊔ (evaluationRangeFunctor j).mapIdem b :=
  (evaluationRangeFunctor j).map_sup a b

def evaluationProductComparison (j : Component) (X Y : Object) :
    EnumerableCarriers.product ((evaluation j).obj X) ((evaluation j).obj Y) ≅
      (evaluation j).obj (product X Y) :=
  eqToIso (by cases j <;> rfl)

theorem evaluation_product (j : Component) {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) :
    (evaluationProductComparison j W Y).hom ≫ (evaluation j).map (productMap f g)=
      EnumerableCarriers.partialProdMap ((evaluation j).map f) ((evaluation j).map g) ≫
        (evaluationProductComparison j X Z).hom := by
  cases j <;> simp only [evaluationProductComparison,eqToIso_refl,Iso.refl_hom,
    Category.id_comp,Category.comp_id] <;> rfl

theorem evaluation_first (j : Component) (X Y : Object) :
    (evaluationProductComparison j X Y).hom ≫ (evaluation j).map (first X Y)=
      EnumerableCarriers.partialFst ((evaluation j).obj X) ((evaluation j).obj Y) := by
  cases j <;> simp only [evaluationProductComparison,eqToIso_refl,Iso.refl_hom,
    Category.id_comp] <;> rfl

theorem evaluation_second (j : Component) (X Y : Object) :
    (evaluationProductComparison j X Y).hom ≫ (evaluation j).map (second X Y)=
      EnumerableCarriers.partialSnd ((evaluation j).obj X) ((evaluation j).obj Y) := by
  cases j <;> simp only [evaluationProductComparison,eqToIso_refl,Iso.refl_hom,
    Category.id_comp] <;> rfl

theorem evaluation_diagonal (j : Component) (X : Object) :
    (evaluation j).map (diagonal X)=EnumerableCarriers.partialDiag ((evaluation j).obj X) ≫
      (evaluationProductComparison j X X).hom := by
  cases j <;> simp only [evaluationProductComparison,eqToIso_refl,Iso.refl_hom,
    Category.comp_id] <;> rfl

theorem evaluation_coproduct (j : Component) {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) :
    ((evaluationRangeFunctor j).comparison W Y).hom ≫ (evaluation j).map (coproductMap f g)=
      coprod_map ((evaluation j).map f) ((evaluation j).map g) ≫
        ((evaluationRangeFunctor j).comparison X Z).hom :=
  (evaluationRangeFunctor j).comparison_sum f g

theorem carrier_induced_restriction {X Y : Carrier} (f : X ⟶ Y) :
    PCategoryStruct.rst f=RestrictionCategory.rst f := by
  change @RestrictionCategory.rst Carrier _ PCategory.inducedRestriction X Y f=_
  rw [EnumerableCarriers.inducedRestriction_eq]

/-- The endpoint component is universal for every c.e. parameter carrier. -/
theorem endpoint_isTuring : RecursionCategory.IsTuringMorphism endpointEvaluator := by
  intro X f
  refine ⟨endpointEncoding (specialize (program f)) (specialize_computable (program f)),?_,
    endpoint_parameterization f⟩
  change PCategoryStruct.rst (endpointEncoding (specialize (program f))
    (specialize_computable (program f)))=𝟙 X
  rw [carrier_induced_restriction]
  exact EnumerableCarriers.totalFromFunction_total _ _ _

theorem left_evaluation_turing :
    RecursionCategory.IsTuringMorphism ((evaluation .left).map tau) := endpoint_isTuring

theorem right_evaluation_turing :
    RecursionCategory.IsTuringMorphism ((evaluation .right).map tau) := endpoint_isTuring

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
