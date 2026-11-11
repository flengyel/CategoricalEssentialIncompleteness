/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConsistentFirstOrderTheories

/-! # Statement checks for the free first-order adjunction -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}
open FirstOrderPresentation

example (P : FirstOrderPresentation V)
    {A B : Subobject P.syntaxData.sentenceObject} (h : A ≤ B) (hB : P.Consistent B) :
    P.Consistent A :=
  FirstOrderPresentation.consistent_of_le P h hB

#print axioms
  CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.consistent_of_le

example {P Q : FirstOrderPresentation V}
    (σ : Translation P Q) (A : Subobject Q.syntaxData.sentenceObject) (hA : Q.Consistent A) :
    P.Consistent ((Subobject.pullback σ.sentence).obj A) :=
  FirstOrderPresentation.Translation.inverse_consistent σ A hA

#print axioms
  CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.inverse_consistent

example {A B : ConsistentTheoryCategory (D := D) (V := V)}
    (σ : A.presentation.Translation B.presentation) :
    (Subobject.«exists» σ.sentence).obj A.theory.val ≤ B.theory.val ↔
      (σ.pushforward.obj A.theory).val ≤ B.theory.val :=
  FirstOrderPresentation.ConsistentTheoryCategory.morphism_bound_iff σ

#print axioms
  CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.ConsistentTheoryCategory.morphism_bound_iff
