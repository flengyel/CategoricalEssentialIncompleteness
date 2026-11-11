/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderTranslationReflection

/-! # Consistent sentence theories and inverse images of translations -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FirstOrderPresentation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}

def Consistent (P : FirstOrderPresentation V) (A : Subobject P.syntaxData.sentenceObject) : Prop :=
  A ⊓ (Subobject.pullback P.syntaxData.sentenceNegation).obj A = ⊥

theorem consistent_of_le (P : FirstOrderPresentation V)
    {A B : Subobject P.syntaxData.sentenceObject} (h : A ≤ B) (hB : P.Consistent B) :
    P.Consistent A := by
  have hn := leOfHom ((Subobject.pullback P.syntaxData.sentenceNegation).map (homOfLE h))
  exact le_antisymm ((inf_le_inf h hn).trans hB.le) bot_le

theorem Translation.inverse_consistent {P Q : FirstOrderPresentation V}
    (σ : Translation P Q) (A : Subobject Q.syntaxData.sentenceObject) (hA : Q.Consistent A) :
    P.Consistent ((Subobject.pullback σ.sentence).obj A) := by
  have hn : (Subobject.pullback P.syntaxData.sentenceNegation).obj
      ((Subobject.pullback σ.sentence).obj A) =
      (Subobject.pullback σ.sentence).obj
        ((Subobject.pullback Q.syntaxData.sentenceNegation).obj A) := by
    rw [← Subobject.pullback_comp, σ.sentence_negation, Subobject.pullback_comp]
  dsimp only [Consistent] at hA ⊢
  rw [hn, ← Subobject.inf_pullback, hA, PresentationLemmas.pullback_bot]

def TheoryConsistent : ObjectProperty (Axioms.TheoryCategory (D := D) (V := V)) :=
  fun A => A.obj.presentation.Consistent A.obj.axioms

abbrev ConsistentTheoryCategory := (TheoryConsistent (D := D) (V := V)).FullSubcategory

namespace ConsistentTheoryCategory

variable (A : ConsistentTheoryCategory (D := D) (V := V))

def presentation : FirstOrderPresentation V := A.obj.obj.presentation

def theory : A.presentation.Theories := ⟨A.obj.obj.axioms, A.obj.property⟩

theorem consistent : A.presentation.Consistent A.theory.val := A.property

theorem morphism_bound_iff {A B : ConsistentTheoryCategory (D := D) (V := V)}
    (σ : A.presentation.Translation B.presentation) :
    (Subobject.«exists» σ.sentence).obj A.theory.val ≤ B.theory.val ↔
      (σ.pushforward.obj A.theory).val ≤ B.theory.val := by
  change (Subobject.«exists» σ.sentence).obj A.theory.val ≤ B.theory.val ↔
    FirstOrderReflection.generated B.presentation.proofs
      ((Subobject.«exists» σ.sentence).obj A.theory.val) ≤ B.theory.val
  exact (FirstOrderReflection.generated_le_iff B.presentation.proofs
    B.presentation.initial _ B.theory).symm

def homMk {A B : ConsistentTheoryCategory (D := D) (V := V)}
    (σ : A.presentation.Translation B.presentation)
    (h : (σ.pushforward.obj A.theory).val ≤ B.theory.val) : A ⟶ B :=
  ObjectProperty.homMk (ObjectProperty.homMk ⟨σ, (morphism_bound_iff σ).mpr h⟩)

end ConsistentTheoryCategory

namespace Axioms

def sentenceFunctor : Axioms (D := D) V ⥤ D where
  obj A := A.presentation.syntaxData.sentenceObject
  map f := f.translation.sentence
  map_id _ := rfl
  map_comp _ _ := rfl

end Axioms

def sentenceFunctor : FirstOrderPresentation (D := D) V ⥤ D where
  obj P := P.syntaxData.sentenceObject
  map f := f.sentence
  map_id _ := rfl
  map_comp _ _ := rfl

def consistentSentenceFunctor : ConsistentTheoryCategory (D := D) (V := V) ⥤ D :=
  TheoryConsistent.ι ⋙ Axioms.IsTheory.ι ⋙ Axioms.sentenceFunctor

end CategoricalEssentialIncompleteness.V46.FirstOrderPresentation
