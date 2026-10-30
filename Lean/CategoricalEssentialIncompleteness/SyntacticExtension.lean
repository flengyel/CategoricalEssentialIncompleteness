/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.SyntacticInseparability

/-! # Theory extension for uniformly provable program categories -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.CodedObjectMembership FailureOfComposition

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticExtension

variable (T T' : ArithmeticTheory) [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [T ⪯ T']

/-- Theory extension keeps every external program index unchanged. -/
def programMap : ProgramQuotient T →* ProgramQuotient T' where
  toFun := Quotient.map id (fun _ _ h => WeakerThan.pbl (𝓢 := T) (𝓣 := T') h)
  map_one' := rfl
  map_mul' q r := Quotient.inductionOn₂ q r (fun _ _ => rfl)

@[simp] theorem programMap_class (q : ℕ) :
    programMap T T' (classOf T q) = classOf T' q := rfl

@[simp] theorem programMap_object (Q : STObjectCode) :
    programMap T T' (objectIdempotent T Q) = objectIdempotent T' Q := rfl

def functor : CodedProgramCategory T ⥤ CodedProgramCategory T' where
  obj Q := object T' (objectCode Q)
  map {Q R} f := ⟨programMap T T' f.val, by
    constructor
    · change objectIdempotent T' (objectCode R) * programMap T T' f.val = _
      rw [← programMap_object T T', ← map_mul, f.property.1]
    · change programMap T T' f.val * objectIdempotent T' (objectCode Q) = _
      rw [← programMap_object T T', ← map_mul, f.property.2]⟩
  map_id Q := CodedHom.ext (programMap_object T T' (objectCode Q))
  map_comp f g := CodedHom.ext ((programMap T T').map_mul g.val f.val)

@[simp] theorem map_index (Q R : STObjectCode) (q : ℕ) :
    (functor T T').map (arrowOfIndex T Q R q) = arrowOfIndex T' Q R q := by
  apply CodedHom.ext
  change programMap T T' (arrowOfIndex T Q R q).val = (arrowOfIndex T' Q R q).val
  rw [arrowOfIndex_val, arrowOfIndex_val, programMap_class]

theorem map_restriction {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (functor T T').map (RestrictionCategory.rst f) =
      RestrictionCategory.rst ((functor T T').map f) := by
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  rw [TypedNearProduct.restrictionCategory_rst_arrowOfIndex, map_index, map_index,
    TypedNearProduct.restrictionCategory_rst_arrowOfIndex]

theorem map_range {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (functor T T').map (Ranges.range f).hom =
      (Ranges.range ((functor T T').map f)).hom := by
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  change (functor T T').map (HasRanges.ran (arrowOfIndex T _ _ q)) =
    HasRanges.ran ((functor T T').map (arrowOfIndex T _ _ q))
  rw [TypedRanges.ran_arrowOfIndex, map_index, map_index, TypedRanges.ran_arrowOfIndex]

theorem map_zero (Q R : CodedProgramCategory T) : (functor T T').map (0 : Q ⟶ R) = 0 := by
  change (functor T T').map (arrowOfIndex T (objectCode Q) (objectCode R)
    ConcreteEmptyGraph.concreteEmptyIndex) = _
  exact map_index T T' _ _ _

open CoprodStruct CategoryTheory.HasCoproducts

@[simp] theorem map_i0 (Q R : CodedProgramCategory T) :
    (functor T T').map (i0 Q R) = i0 ((functor T T').obj Q) ((functor T T').obj R) :=
  map_index T T' _ _ _

@[simp] theorem map_i1 (Q R : CodedProgramCategory T) :
    (functor T T').map (i1 Q R) = i1 ((functor T T').obj Q) ((functor T T').obj R) :=
  map_index T T' _ _ _

theorem comparison_eq_id (Q R : CodedProgramCategory T) :
    coproductComparison (functor T T') Q R =
      𝟙 (coprod ((functor T T').obj Q) ((functor T T').obj R)) := by
  rw [coproductComparison, map_i0, map_i1, copair_i0_i1]

/-- The theory-extension functor is a range functor. -/
def rangeFunctor : RangeFunctor (CodedProgramCategory T) (CodedProgramCategory T') where
  toFunctor := functor T T'
  map_restrict := map_restriction T T'
  map_range := map_range T T'
  map_zero := map_zero T T'
  comparison_isIso Q R := by rw [comparison_eq_id]; infer_instance

theorem map_product {Q R S V : CodedProgramCategory T} (f : Q ⟶ R) (g : S ⟶ V) :
    (functor T T').map (PCategoryStruct.nearProd_map f g) =
      PCategoryStruct.nearProd_map ((functor T T').map f) ((functor T T').map g) := by
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  obtain ⟨r, rfl⟩ := exists_arrowOfIndex T (objectCode S) (objectCode V) g
  rw [TypedNearProduct.nearProd_map_arrowOfIndex, map_index, map_index, map_index,
    TypedNearProduct.nearProd_map_arrowOfIndex]

theorem map_diagonal (Q : CodedProgramCategory T) :
    (functor T T').map (PCategoryStruct.diag Q) =
      PCategoryStruct.diag ((functor T T').obj Q) := map_index T T' _ _ _

theorem map_turing : (functor T T').map (TypedTuringMorphism.typedTau T) =
    TypedTuringMorphism.typedTau T' := map_index T T' _ _ _

theorem map_sum {W X Y Z : CodedProgramCategory T} (f : W ⟶ X) (g : Y ⟶ Z) :
    (functor T T').map (coprod_map f g) =
      coprod_map ((functor T T').map f) ((functor T T').map g) := by
  have h := (rangeFunctor T T').comparison_sum f g
  change coproductComparison (functor T T') W Y ≫ (functor T T').map (coprod_map f g) =
    coprod_map ((functor T T').map f) ((functor T T').map g) ≫
      coproductComparison (functor T T') X Z at h
  simpa only [RangeFunctor.comparison_hom, comparison_eq_id,
    Category.id_comp, Category.comp_id] using h

theorem map_summand0 (Q R : CodedProgramCategory T) :
    (functor T T').map (summand0 Q R).hom =
      (summand0 ((functor T T').obj Q) ((functor T T').obj R)).hom := by
  change (functor T T').map (coprod_map (𝟙 Q) (0 : R ⟶ R)) =
    coprod_map (𝟙 ((functor T T').obj Q))
      (0 : (functor T T').obj R ⟶ (functor T T').obj R)
  rw [map_sum, (functor T T').map_id, map_zero]

theorem map_summand1 (Q R : CodedProgramCategory T) :
    (functor T T').map (summand1 Q R).hom =
      (summand1 ((functor T T').obj Q) ((functor T T').obj R)).hom := by
  change (functor T T').map (coprod_map (0 : Q ⟶ Q) (𝟙 R)) =
    coprod_map (0 : (functor T T').obj Q ⟶ (functor T T').obj Q)
      (𝟙 ((functor T T').obj R))
  rw [map_sum, map_zero, (functor T T').map_id]

theorem map_coding_iso :
    (functor T T').map (TypedRecursionCategory.omegaCoprodIso T).symm.hom =
      (TypedRecursionCategory.omegaCoprodIso T').symm.hom := map_index T T' _ _ _

theorem pair0_image :
    (rangeFunctor T T').mapIdem (SyntacticModel.syntacticPair0 T) =
      SyntacticModel.syntacticPair0 T' := by
  apply Idem.ext
  change (functor T T').map (RestrictionCategory.rst
    ((PCategoryStruct.diag _ ≫ TypedTuringMorphism.typedTau T ≫
      (TypedRecursionCategory.omegaCoprodIso T).symm.hom) ≫ (summand0 _ _).hom)) = _
  rw [map_restriction, (functor T T').map_comp, (functor T T').map_comp,
    (functor T T').map_comp, map_diagonal, map_turing, map_coding_iso, map_summand0]
  rfl

theorem pair1_image :
    (rangeFunctor T T').mapIdem (SyntacticModel.syntacticPair1 T) =
      SyntacticModel.syntacticPair1 T' := by
  apply Idem.ext
  change (functor T T').map (RestrictionCategory.rst
    ((PCategoryStruct.diag _ ≫ TypedTuringMorphism.typedTau T ≫
      (TypedRecursionCategory.omegaCoprodIso T).symm.hom) ≫ (summand1 _ _).hom)) = _
  rw [map_restriction, (functor T T').map_comp, (functor T T').map_comp,
    (functor T T').map_comp, map_diagonal, map_turing, map_coding_iso, map_summand1]
  rfl

/-- The images are the identical categorical diagonal pair in every
consistent extension. -/
theorem extension_pair_inseparable (hT' : Consistent T') :
    Inseparable ((rangeFunctor T T').mapIdem (SyntacticModel.syntacticPair0 T))
      ((rangeFunctor T T').mapIdem (SyntacticModel.syntacticPair1 T)) := by
  rw [pair0_image, pair1_image]
  exact SyntacticModel.syntactic_inseparable T' hT'

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticExtension
