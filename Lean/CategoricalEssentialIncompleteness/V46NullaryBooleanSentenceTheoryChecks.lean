/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSentenceTheory

/-! # Statement checks for NullaryBooleanSentenceTheory -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)
open NullaryBooleanValuation

example : sentenceTheory S d ⊓
    (Subobject.pullback S.sentenceNegation).obj (sentenceTheory S d) = ⊥ := sentence_consistent S d
example : sentenceTheory S d ⊔
    (Subobject.pullback S.sentenceNegation).obj (sentenceTheory S d) = ⊤ := sentence_complete S d
example (proofs : (A : Subobject S.sentenceObject) →
    Endofunctor.Algebra (S.logicalRules A.arrow).inference) (initial : ∀ A, IsInitial (proofs A)) :
    FirstOrderReflection.generated proofs (sentenceTheory S d) = sentenceTheory S d :=
  sentence_closed S d proofs initial

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.sentence_negation_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.sentence_consistent
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.sentence_complete
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.sentence_closed
