/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryPresentationAdjunction

/-! # Statement checks for the free first-order adjunction -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}
variable (F : NullaryPresentations V)

example : F.functor ⊣ FirstOrderPresentation.sentenceFunctor :=
  NullaryPresentations.adjunction F

example (X : D) (R : FirstOrderPresentation V) :
    (F.functor.obj X ⟶ R) ≃ (X ⟶ R.syntaxData.sentenceObject) := F.homEquiv X R

#print axioms CategoricalEssentialIncompleteness.V46.NullaryPresentations.adjunction
#print axioms CategoricalEssentialIncompleteness.V46.NullaryPresentations.homEquiv
