/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderGeneration

/-! # Statement checks for generation and its two adjunctions -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.FirstOrderGeneration

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S : D}
variable {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : {A : D} → (a : A ⟶ S) →
  Endofunctor.Algebra (firstOrderRules logical sentence a all imp).inference)
variable (proofInitial : ∀ {A : D} (a : A ⟶ S), IsInitial (proofs a))

include proofInitial in
example (A B : Subobject S) (hB : IsClosed proofs B) :
    generated proofs A ≤ B ↔ A ≤ B :=
  generated_le_iff proofs proofInitial A B hB

include proofInitial in
example : GaloisConnection (fun A => (generation proofs proofInitial).obj A)
    (fun B => (inclusion proofs).obj B) :=
  generation_galois proofs proofInitial

include proofInitial in
example : generation proofs proofInitial ⊣ inclusion proofs :=
  adjunction proofs proofInitial

include proofInitial in
example (A : Over S) (B : ClosedTheory proofs) :
    ((presentationGeneration proofs proofInitial).obj A ⟶ B) ≃
      (A ⟶ (presentationInclusion proofs).obj B) :=
  presentationHomEquiv proofs proofInitial A B

include proofInitial in
example : presentationGeneration proofs proofInitial ⊣ presentationInclusion proofs :=
  presentationAdjunction proofs proofInitial

#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderGeneration.generation_galois
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderGeneration.adjunction
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderGeneration.presentationAdjunction
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderGeneration.theory_closed
