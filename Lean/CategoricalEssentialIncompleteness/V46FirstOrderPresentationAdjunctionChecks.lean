/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderPresentationAdjunction

/-! # Reflection into arbitrary closed monic sentence presentations -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.FirstOrderPresentations

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S : D}
variable {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : {A : D} → (a : A ⟶ S) →
  Endofunctor.Algebra (firstOrderRules logical sentence a all imp).inference)
variable (proofInitial : ∀ {A : D} (a : A ⟶ S), IsInitial (proofs a))

example : (inclusion proofs).Full := inferInstance

example : (inclusion proofs).Faithful := inferInstance

example (B : TheoryCategory proofs) : Mono B.obj.hom := mono proofs B

include proofInitial in
example (A : Over S) (B : TheoryCategory proofs) :
    ((generation proofs proofInitial).obj A ⟶ B) ≃
      (A ⟶ (inclusion proofs).obj B) :=
  homEquiv proofs proofInitial A B

include proofInitial in
example : generation proofs proofInitial ⊣ inclusion proofs :=
  adjunction proofs proofInitial

#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentations.generation
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentations.homEquiv
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentations.adjunction
