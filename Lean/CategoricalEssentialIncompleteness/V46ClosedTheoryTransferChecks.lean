/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SliceClosedTheories

/-! # Explicit checks of constructed closed-theory transport

The general rule-algebra construction and its ordinary-slice instances
are checked independently of pending manuscript revisions.
-/

@[expose] public section
noncomputable section

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

section General
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (G : C ⥤ D) [PreservesFiniteLimits G]
variable {F : C} {N : ℕ} (R : RulePresentation F N)

example (Q : Over F) (i : Fin (N + 1)) : G.obj (R.ruleObject Q i) ≅
    (FiniteRuleTransport.mappedRules G R).ruleObject ((Over.post G).obj Q) i :=
  FiniteRuleTransport.ruleObjectIso G R Q i

example {M : C} (m : M ⟶ F) (hm : ClosedUnder R.inference m) :
    ClosedUnder (FiniteRuleTransport.mappedRules G R).inference (G.map m) :=
  FiniteRuleTransport.map_closed G R m hm

variable {V L S : C} {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : (A : Subobject S) →
  Endofunctor.Algebra (firstOrderRules logical sentence A.arrow all imp).inference)
variable (proofInitial : ∀ A, IsInitial (proofs A))
variable (targetProofs : (B : Subobject (G.obj S)) →
  Endofunctor.Algebra (firstOrderRules (G.map logical) (G.map sentence) B.arrow
    (FirstOrderRuleTransport.mappedAll G all) (FirstOrderRuleTransport.mappedImp G imp)).inference)
variable (targetInitial : ∀ B, IsInitial (targetProofs B))

example (A : Subobject S) :
    FirstOrderReflection.generated targetProofs (FiniteLimitSubobjects.object G A) ≤
      FiniteLimitSubobjects.object G (FirstOrderReflection.generated proofs A) :=
  ClosedTheoryTransfer.generation_le_image G proofs proofInitial targetProofs targetInitial A

example (A : Subobject S) (hA : FirstOrderReflection.generated proofs A = A) :
    FirstOrderReflection.generated targetProofs (FiniteLimitSubobjects.object G A) =
      FiniteLimitSubobjects.object G A :=
  ClosedTheoryTransfer.closed_image G proofs proofInitial targetProofs targetInitial A hA

example : FirstOrderReflection.Theory proofs ⥤ FirstOrderReflection.Theory targetProofs :=
  ClosedTheoryTransfer.theoryFunctor G proofs proofInitial targetProofs targetInitial

end General

section Slices
variable {C : Type u₁} [Category.{v₁} C] [Regular C] [HasFiniteCoproducts C]

example (U : C) : Regular (Over U) := RegularSlices.regular U
example [FinitaryExtensive C] (U : C) : FinitaryExtensive (Over U) :=
  RegularSlices.finitaryExtensive U
example (U : C) : Over.forget U ⊣ constantFamilyFunctor U :=
  SliceBaseChangeGeometry.forgetAdjunction U
example (U : C) : PreservesFiniteLimits (constantFamilyFunctor U) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U
example {Z U : C} (point : Z ⟶ U) (hZ : IsTerminal Z) :
    PreservesFiniteLimits (SliceBaseChangeGeometry.evaluation point hZ) :=
  SliceBaseChangeGeometry.evaluation_preservesFiniteLimits point hZ

attribute [local instance] SliceClosedTheories.sliceRegular SliceClosedTheories.constantLimits
  SliceClosedTheories.evaluationLimits

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

example (T : FirstOrderReflection.Theory proofs) :
    FirstOrderReflection.generated sliceProofs
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) T.val) =
      FiniteLimitSubobjects.object (constantFamilyFunctor U) T.val :=
  SliceClosedTheories.constant_closed U proofs proofInitial sliceProofs sliceInitial
    T.val T.property

end Slices

section Evaluation
variable {C : Type u₁} [Category.{v₁} C] [Regular C] [HasFiniteCoproducts C]
attribute [local instance] SliceClosedTheories.sliceRegular SliceClosedTheories.evaluationLimits
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

example (T : FirstOrderReflection.Theory proofs) :
    FirstOrderReflection.generated evaluatedProofs
        (FiniteLimitSubobjects.object (SliceBaseChangeGeometry.evaluation point hZ) T.val) =
      FiniteLimitSubobjects.object (SliceBaseChangeGeometry.evaluation point hZ) T.val :=
  SliceClosedTheories.evaluation_closed point hZ proofs proofInitial
    evaluatedProofs evaluatedInitial T.val T.property

end Evaluation

#print axioms FiniteRuleTransport.powerIso
#print axioms FiniteRuleTransport.power_naturality
#print axioms FiniteRuleTransport.ruleObjectIso
#print axioms FiniteRuleTransport.ruleObjectIso_conclusion
#print axioms FiniteRuleTransport.mappedStructure
#print axioms FiniteRuleTransport.mappedAlgebra
#print axioms FiniteRuleTransport.map_closed
#print axioms FiniteRuleTransport.map_closed_of_rule_hom
#print axioms FirstOrderRuleTransport.ruleHom
#print axioms FirstOrderRuleTransport.map_closed
#print axioms FiniteLimitSubobjects.object_monotone
#print axioms FiniteLimitSubobjects.object_mk
#print axioms FiniteLimitSubobjects.object_pullback
#print axioms ClosedTheoryTransfer.generation_le_image
#print axioms ClosedTheoryTransfer.closed_image
#print axioms ClosedTheoryTransfer.theoryFunctor
#print axioms RegularSlices.underlying_regularEpi
#print axioms RegularSlices.regularEpi_of_underlying
#print axioms RegularSlices.regular
#print axioms RegularSlices.finitaryExtensive
#print axioms SliceBaseChangeGeometry.forgetAdjunction
#print axioms SliceBaseChangeGeometry.constant_preservesFiniteLimits
#print axioms SliceBaseChangeGeometry.evaluation_preservesFiniteLimits
#print axioms SliceClosedTheories.constant_closed
#print axioms SliceClosedTheories.constantTheoryFunctor
#print axioms SliceClosedTheories.evaluation_closed
#print axioms SliceClosedTheories.evaluationTheoryFunctor
