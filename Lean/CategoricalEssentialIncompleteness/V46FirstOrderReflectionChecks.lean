/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderReflection

/-! # Statement checks for Theorem 4.4 -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.FirstOrderReflection

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S : D}
variable {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : (A : Subobject S) →
  Endofunctor.Algebra (firstOrderRules logical sentence A.arrow all imp).inference)
variable (proofInitial : ∀ A, IsInitial (proofs A))

example (A : Subobject S) : A ≤ generated proofs A := extensive proofs A

include proofInitial in
example : Monotone (generated proofs) := monotone proofs proofInitial

include proofInitial in
example (A : Subobject S) : generated proofs (generated proofs A) = generated proofs A :=
  idempotent proofs proofInitial A

example (A : Subobject S) :
    generated proofs A = (Subobject.pullback sentence).obj (formulaTheory proofs A) :=
  generated_eq_pullback proofs A

include proofInitial in
example (A : Subobject S) (T : Theory proofs) : generated proofs A ≤ T.val ↔ A ≤ T.val :=
  generated_le_iff proofs proofInitial A T

include proofInitial in
example : generation proofs proofInitial ⊣ inclusion proofs := adjunction proofs proofInitial

include proofInitial in
example (a : Over S) : ((presentationGeneration proofs proofInitial).obj a).val =
    generated proofs (imageSubobject a.hom) := presentationGeneration_obj proofs proofInitial a

include proofInitial in
example (a : Over S) (T : Theory proofs) :
    ((presentationGeneration proofs proofInitial).obj a ⟶ T) ≃
      (a ⟶ (presentationInclusion proofs).obj T) := presentationHomEquiv proofs proofInitial a T

include proofInitial in
example : presentationGeneration proofs proofInitial ⊣ presentationInclusion proofs :=
  presentationAdjunction proofs proofInitial

#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderReflection.extensive
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderReflection.monotone
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderReflection.idempotent
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderReflection.generated_eq_pullback
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderReflection.adjunction
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderReflection.presentationAdjunction
