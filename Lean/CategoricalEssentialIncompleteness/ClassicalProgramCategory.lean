/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalProducts

/-! # Classical partial recursive arrows on the formal numerical types

Objects retain their formal type expressions. Arrows are actual partial
functions in the image of standard program evaluation, with equality of
partial-function graphs. Thus no provability quotient remains on arrows.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

open PartialFunctions SyntacticModel

@[simp] theorem Q_product_restriction {X Y : CodedProgramCategory 𝗣𝗔} (f : X ⟶ Y) :
    Q.map (PCategoryStruct.rst f) = PCategoryStruct.rst (Q.map f) := by
  simp only [PCategoryStruct.rst, Q.map_comp, Q.map_id, Q_diag, Q_product, Q_first]

@[simp] theorem Q_rst {X Y : CodedProgramCategory 𝗣𝗔} (f : X ⟶ Y) :
    Q.map (rst f) = rst (Q.map f) := Q_product_restriction f

@[simp] theorem J_rst {X Y : Rec} (f : X ⟶ Y) : J.map (rst f) = rst (J.map f) := by
  obtain ⟨g, rfl⟩ := exists_source f
  rw [← Q_rst]
  exact model_map_restriction 𝗣𝗔 ℕ g

instance : HasZeroMorphisms Rec where
  zero X Y := ⟨⟨0, ⟨0, model_map_zero 𝗣𝗔 ℕ X.base Y.base⟩⟩⟩
  comp_zero := by intros; exact FunctorImage.Hom.ext comp_zero
  zero_comp := by intros; exact FunctorImage.Hom.ext zero_comp

instance : RestrictionZero Rec where
  restrict_zero X Y := by
    apply FunctorImage.Hom.ext
    change J.map (rst (0 : X ⟶ Y)) = 0
    rw [J_rst]
    exact RestrictionZero.restrict_zero _ _

@[simp] theorem Q_zero (X Y : CodedProgramCategory 𝗣𝗔) : Q.map (0 : X ⟶ Y) = 0 :=
  FunctorImage.Hom.ext (model_map_zero 𝗣𝗔 ℕ X Y)

instance : Ranges Rec where
  range f := ⟨⟨(Ranges.range f.val).hom,
    ⟨(Ranges.range (FunctorImage.representative standardFunctor f)).hom, by
      rw [model_map_range, FunctorImage.map_representative]⟩⟩,
    by
      apply (FunctorImage.inclusion standardFunctor).map_injective
      rw [J_rst]
      exact (Ranges.range f.val).restriction⟩
  receives f := FunctorImage.Hom.ext (Ranges.receives f.val)
  agreement f g h he := FunctorImage.Hom.ext
    (Ranges.agreement f.val g.val h.val (congrArg FunctorImage.Hom.val he))

@[simp] theorem Q_range {X Y : CodedProgramCategory 𝗣𝗔} (f : X ⟶ Y) :
    Q.map (Ranges.range f).hom = (Ranges.range (Q.map f)).hom :=
  FunctorImage.Hom.ext (model_map_range 𝗣𝗔 ℕ f)

instance : CoprodStruct Rec where
  coprod X Y := ⟨coprod X.base Y.base⟩
  coprod_map f g := ⟨coprod_map f.val g.val, by
    refine ⟨coprod_map (FunctorImage.representative standardFunctor f)
      (FunctorImage.representative standardFunctor g), ?_⟩
    have he := (modelRangeFunctor 𝗣𝗔 ℕ).comparison_sum
      (FunctorImage.representative standardFunctor f)
      (FunctorImage.representative standardFunctor g)
    change coproductComparison standardFunctor _ _ ≫ standardFunctor.map _ =
      coprod_map (standardFunctor.map _) (standardFunctor.map _) ≫
        coproductComparison standardFunctor _ _ at he
    simpa only [RangeFunctor.comparison_hom, model_comparison_eq_id,
      Category.id_comp, Category.comp_id, FunctorImage.map_representative] using he⟩
  codiag X := ⟨codiag (standardFunctor.obj X.base), by
    refine ⟨codiag X.base, ?_⟩
    have he := (modelRangeFunctor 𝗣𝗔 ℕ).comparison_copair (𝟙 X.base) (𝟙 X.base)
    change coproductComparison standardFunctor _ _ ≫
      standardFunctor.map (copair (𝟙 X.base) (𝟙 X.base)) =
        copair (standardFunctor.map (𝟙 X.base)) (standardFunctor.map (𝟙 X.base)) at he
    rw [standardFunctor.map_id] at he
    simpa only [RangeFunctor.comparison_hom, model_comparison_eq_id,
      Category.id_comp, Functor.map_id, copair, coprod_id] using he⟩
  i0 X Y := ⟨i0 _ _, ⟨i0 X.base Y.base, model_map_i0 𝗣𝗔 ℕ X.base Y.base⟩⟩
  i1 X Y := ⟨i1 _ _, ⟨i1 X.base Y.base, model_map_i1 𝗣𝗔 ℕ X.base Y.base⟩⟩

instance : CategoryTheory.HasCoproducts Rec where
  coprod_id X Y := FunctorImage.Hom.ext (coprod_id _ _)
  coprod_comp f g h k := FunctorImage.Hom.ext (coprod_comp f.val g.val h.val k.val)
  i0_codiag X := FunctorImage.Hom.ext (i0_codiag _)
  i1_codiag X := FunctorImage.Hom.ext (i1_codiag _)
  i0_i1_codiag X Y := FunctorImage.Hom.ext (i0_i1_codiag _ _)
  codiag_nat f := FunctorImage.Hom.ext (codiag_nat f.val)
  i0_nat f := FunctorImage.Hom.ext (i0_nat f.val)
  i0_nat_right f := FunctorImage.Hom.ext (i0_nat_right f.val)
  i1_nat f := FunctorImage.Hom.ext (i1_nat f.val)
  i1_nat_left f := FunctorImage.Hom.ext (i1_nat_left f.val)

def inclusionRangeFunctor : RangeFunctor Rec Pfn where
  toFunctor := J
  map_restrict := J_rst
  map_range _ := rfl
  map_zero _ _ := rfl
  comparison_isIso X Y := by
    have he : coproductComparison J X Y = 𝟙 _ := copair_i0_i1 _ _
    rw [he]
    infer_instance

def quotientRangeFunctor : RangeFunctor (CodedProgramCategory 𝗣𝗔) Rec where
  toFunctor := Q
  map_restrict := Q_rst
  map_range := Q_range
  map_zero := Q_zero
  comparison_isIso X Y := by
    have he : coproductComparison Q X Y = 𝟙 _ := by
      apply FunctorImage.Hom.ext
      exact model_comparison_eq_id 𝗣𝗔 ℕ X Y
    rw [he]
    infer_instance

instance : JoinInverse Rec where
  pull_sup f a b := by
    apply Idem.ext
    apply (FunctorImage.inclusion standardFunctor).map_injective
    exact congrArg Idem.hom (show
      inclusionRangeFunctor.mapIdem (Idem.pull f (a ⊔ b)) =
        inclusionRangeFunctor.mapIdem (Idem.pull f a ⊔ Idem.pull f b) from by
      rw [RangeFunctor.map_pull, RangeFunctor.map_sup, JoinInverse.pull_sup,
        RangeFunctor.map_sup, RangeFunctor.map_pull, RangeFunctor.map_pull])

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
