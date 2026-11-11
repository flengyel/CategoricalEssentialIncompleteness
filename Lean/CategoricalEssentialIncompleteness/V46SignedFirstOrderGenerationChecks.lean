/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFirstOrderGeneration

/-! # Statement checks for the free first-order adjunction -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}
variable (F : NullaryPresentations V) {X : D}
open SignedFirstOrder

example (a b : Subobject X) :
    a ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).obj
        (theory F a b).val ∧
      b ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).obj
        ((Subobject.pullback (F.syntaxData X).sentenceNegation).obj (theory F a b).val) :=
  atomic_bounds F a b

#print axioms
  CategoricalEssentialIncompleteness.V46.SignedFirstOrder.atomic_bounds

example {R : FirstOrderPresentation V}
    (τ : (F.presentation X).Translation R) (a b : Subobject X) (T : R.Theories) :
    (Subobject.«exists» τ.sentence).obj (theory F a b).val ≤ T.val ↔
      (Subobject.«exists» τ.sentence).obj (axioms F a b) ≤ T.val :=
  image_theory_le_iff F τ a b T

#print axioms
  CategoricalEssentialIncompleteness.V46.SignedFirstOrder.image_theory_le_iff

example (R : FirstOrderPresentation V)
    (f : X ⟶ R.syntaxData.sentenceObject) (a b : Subobject X) (T : R.Theories) :
    (Subobject.«exists» (F.interpretation R f).sentence).obj (theory F a b).val ≤ T.val ↔
      a ≤ (Subobject.pullback f).obj T.val ∧
      b ≤ (Subobject.pullback f).obj
        ((Subobject.pullback R.syntaxData.sentenceNegation).obj T.val) :=
  interpretation_theory_bound F R f a b T

#print axioms
  CategoricalEssentialIncompleteness.V46.SignedFirstOrder.interpretation_theory_bound

example (R : FirstOrderPresentation V) (T : R.Theories)
    (hc : R.Consistent T.val) :
    (F.presentation R.syntaxData.sentenceObject).Consistent
      (theory F T.val ((Subobject.pullback R.syntaxData.sentenceNegation).obj T.val)).val :=
  evaluation_consistent F R T hc

#print axioms
  CategoricalEssentialIncompleteness.V46.SignedFirstOrder.evaluation_consistent
