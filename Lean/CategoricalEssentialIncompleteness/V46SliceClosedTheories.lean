/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ClosedTheoryTransfer
public import CategoricalEssentialIncompleteness.V46RegularSlices
public import CategoricalEssentialIncompleteness.V46SliceBaseChangeGeometry

/-! # Constructed closure transfer for constant families and slice evaluation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SliceClosedTheories

variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]
local instance sliceRegular (P : C) : Regular (Over P) := RegularSlices.regular P
local instance constantLimits (P : C) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P
local instance evaluationLimits {Z U : C} (point : Z ⟶ U) (hZ : IsTerminal Z) :
    PreservesFiniteLimits (SliceBaseChangeGeometry.evaluation point hZ) :=
  SliceBaseChangeGeometry.evaluation_preservesFiniteLimits point hZ

section Constants

variable (U : C) {V F L S : C} {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : (A : Subobject S) →
  Endofunctor.Algebra (firstOrderRules logical sentence A.arrow all imp).inference)
variable (proofInitial : ∀ A, IsInitial (proofs A))
variable (sliceProofs : (B : Subobject ((constantFamilyFunctor U).obj S)) →
  Endofunctor.Algebra (firstOrderRules ((constantFamilyFunctor U).map logical)
    ((constantFamilyFunctor U).map sentence) B.arrow
    (FirstOrderRuleTransport.mappedAll (constantFamilyFunctor U) all)
    (FirstOrderRuleTransport.mappedImp (constantFamilyFunctor U) imp)).inference)
variable (sliceInitial : ∀ B, IsInitial (sliceProofs B))

def constantTheoryFunctor : FirstOrderReflection.Theory proofs ⥤
    FirstOrderReflection.Theory sliceProofs :=
  ClosedTheoryTransfer.theoryFunctor (constantFamilyFunctor U) proofs proofInitial
    sliceProofs sliceInitial

include proofInitial sliceInitial in
theorem constant_closed (A : Subobject S) (hA : FirstOrderReflection.generated proofs A = A) :
    FirstOrderReflection.generated sliceProofs
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) A) =
      FiniteLimitSubobjects.object (constantFamilyFunctor U) A :=
  ClosedTheoryTransfer.closed_image (constantFamilyFunctor U) proofs proofInitial
    sliceProofs sliceInitial A hA

end Constants

section Evaluation

variable {Z U : C} (point : Z ⟶ U) (hZ : IsTerminal Z)
variable {V F L S : Over U} {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : (A : Subobject S) →
  Endofunctor.Algebra (firstOrderRules logical sentence A.arrow all imp).inference)
variable (proofInitial : ∀ A, IsInitial (proofs A))
variable (evaluatedProofs :
  (B : Subobject ((SliceBaseChangeGeometry.evaluation point hZ).obj S)) →
    Endofunctor.Algebra (firstOrderRules
      ((SliceBaseChangeGeometry.evaluation point hZ).map logical)
      ((SliceBaseChangeGeometry.evaluation point hZ).map sentence) B.arrow
      (FirstOrderRuleTransport.mappedAll (SliceBaseChangeGeometry.evaluation point hZ) all)
      (FirstOrderRuleTransport.mappedImp
        (SliceBaseChangeGeometry.evaluation point hZ) imp)).inference)
variable (evaluatedInitial : ∀ B, IsInitial (evaluatedProofs B))

def evaluationTheoryFunctor : FirstOrderReflection.Theory proofs ⥤
    FirstOrderReflection.Theory evaluatedProofs :=
  ClosedTheoryTransfer.theoryFunctor (SliceBaseChangeGeometry.evaluation point hZ) proofs
    proofInitial evaluatedProofs evaluatedInitial

include proofInitial evaluatedInitial in
theorem evaluation_closed (A : Subobject S)
    (hA : FirstOrderReflection.generated proofs A = A) :
    FirstOrderReflection.generated evaluatedProofs
        (FiniteLimitSubobjects.object (SliceBaseChangeGeometry.evaluation point hZ) A) =
      FiniteLimitSubobjects.object (SliceBaseChangeGeometry.evaluation point hZ) A :=
  ClosedTheoryTransfer.closed_image (SliceBaseChangeGeometry.evaluation point hZ) proofs
    proofInitial evaluatedProofs evaluatedInitial A hA

end Evaluation

end CategoricalEssentialIncompleteness.V46.SliceClosedTheories
