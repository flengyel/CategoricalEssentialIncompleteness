/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SliceSubobjectPredicates
public import CategoricalEssentialIncompleteness.V46OrdinaryEvaluationRetraction

/-! # Evaluation of arbitrary slice subobjects in the original coordinates -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SliceSubobjectPredicates

variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]
variable {Z U : C} (point : Z ⟶ U) (hZ : IsTerminal Z)
local instance evaluationSliceRegular (P : C) : Regular (Over P) := RegularSlices.regular P
local instance evaluationLimits :
    PreservesFiniteLimits (SliceBaseChangeGeometry.evaluation point hZ) :=
  SliceBaseChangeGeometry.evaluation_preservesFiniteLimits point hZ

omit [HasFiniteCoproducts C] in
theorem evaluation_square {A B : Over U} (f : A ⟶ B) :
    IsPullback ((SliceBaseChangeGeometry.evaluation point hZ).map f)
      (pullback.fst A.hom point) (pullback.fst B.hom point) f.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd B.hom point) (h₂₂ := B.hom)
  · have hs : (SliceBaseChangeGeometry.evaluation point hZ).map f ≫
          pullback.snd B.hom point = pullback.snd A.hom point := by
      simp [SliceBaseChangeGeometry.evaluation, Over.pullback]
    rw [hs, Over.w f]
    exact (IsPullback.of_hasPullback A.hom point).flip
  · simp [SliceBaseChangeGeometry.evaluation, Over.pullback]
  · exact (IsPullback.of_hasPullback B.hom point).flip

omit [HasFiniteCoproducts C] in
theorem evaluation_object {A : Over U} (W : Subobject A) :
    FiniteLimitSubobjects.object (SliceBaseChangeGeometry.evaluation point hZ) W =
      (Subobject.pullback (pullback.fst A.hom point)).obj (underlying W) := by
  have hW : underlying W = Subobject.mk W.arrow.left :=
    (congrArg underlying (Subobject.mk_arrow W)).symm
  rw [hW]
  exact (Subobject.pullback_obj_mk (evaluation_square point hZ W.arrow).flip).symm

omit [HasFiniteCoproducts C] in
theorem evaluate_eq_retraction {S : C} (W : Subobject (constantFamily U S)) :
    evaluate point hZ W =
      (Subobject.pullback (SliceBaseChangeGeometry.evaluationConstantIso point hZ S).inv).obj
        (FiniteLimitSubobjects.object (SliceBaseChangeGeometry.evaluation point hZ) W) := by
  rw [evaluation_object, ← Subobject.pullback_comp,
    SliceBaseChangeGeometry.evaluationConstantIso_inv_fst]
  rfl

omit [HasFiniteCoproducts C] in
theorem evaluate_monotone {S : C} : Monotone (evaluate point hZ (S := S)) := by
  intro T W h
  exact (Subobject.pullback (fiber point hZ S)).monotone ((orderIso _).monotone h)

end CategoricalEssentialIncompleteness.V46.SliceSubobjectPredicates
