/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryPresentationAdjunction

/-! # Generating a first-order theory by asserting and refuting propositional atoms -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SignedFirstOrder

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} (F : NullaryPresentations V) {X : D}

def axioms (a b : Subobject X) : Subobject (F.presentation X).syntaxData.sentenceObject :=
  (Subobject.«exists» (NullaryInterpretation.atomSentence (F.syntaxData X))).obj a ⊔
    (Subobject.«exists» (NullaryInterpretation.atomSentence (F.syntaxData X) ≫
      (F.syntaxData X).sentenceNegation)).obj b

def theory (a b : Subobject X) : (F.presentation X).Theories :=
  ⟨FirstOrderReflection.generated (F.presentation X).proofs (axioms F a b),
    FirstOrderReflection.idempotent (F.presentation X).proofs (F.presentation X).initial _⟩

theorem atomic_bounds (a b : Subobject X) :
    a ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).obj
        (theory F a b).val ∧
      b ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).obj
        ((Subobject.pullback (F.syntaxData X).sentenceNegation).obj (theory F a b).val) := by
  have he : axioms F a b ≤ (theory F a b).val :=
    FirstOrderReflection.extensive (F.presentation X).proofs (axioms F a b)
  constructor
  · exact (Subobject.existsPullbackAdj
      (NullaryInterpretation.atomSentence (F.syntaxData X))).gc _ _ |>.mp
        ((le_sup_left : _ ≤ axioms F a b).trans he)
  · have hb := (Subobject.existsPullbackAdj
      (NullaryInterpretation.atomSentence (F.syntaxData X) ≫
        (F.syntaxData X).sentenceNegation)).gc _ _ |>.mp
        ((le_sup_right : _ ≤ axioms F a b).trans he)
    simpa only [Subobject.pullback_comp] using hb

theorem image_axioms_le_iff {R : FirstOrderPresentation V}
    (τ : (F.presentation X).Translation R) (a b : Subobject X)
    (B : Subobject R.syntaxData.sentenceObject) :
    (Subobject.«exists» τ.sentence).obj (axioms F a b) ≤ B ↔
      a ≤ (Subobject.pullback
        (NullaryInterpretation.atomSentence (F.syntaxData X) ≫ τ.sentence)).obj B ∧
      b ≤ (Subobject.pullback
        ((NullaryInterpretation.atomSentence (F.syntaxData X) ≫
          (F.syntaxData X).sentenceNegation) ≫ τ.sentence)).obj B := by
  have h := (Subobject.existsPullbackAdj τ.sentence).gc (axioms F a b) B
  rw [h, axioms, sup_le_iff]
  have hp := (Subobject.existsPullbackAdj
    (NullaryInterpretation.atomSentence (F.syntaxData X))).gc a
      ((Subobject.pullback τ.sentence).obj B)
  have hn := (Subobject.existsPullbackAdj
    (NullaryInterpretation.atomSentence (F.syntaxData X) ≫
      (F.syntaxData X).sentenceNegation)).gc b ((Subobject.pullback τ.sentence).obj B)
  simpa only [Subobject.pullback_comp] using and_congr hp hn

theorem image_theory_le_iff {R : FirstOrderPresentation V}
    (τ : (F.presentation X).Translation R) (a b : Subobject X) (T : R.Theories) :
    (Subobject.«exists» τ.sentence).obj (theory F a b).val ≤ T.val ↔
      (Subobject.«exists» τ.sentence).obj (axioms F a b) ≤ T.val := by
  constructor
  · intro h
    exact (leOfHom ((Subobject.«exists» τ.sentence).map
      (homOfLE (FirstOrderReflection.extensive (F.presentation X).proofs (axioms F a b))))).trans h
  · intro h
    have hg := τ.map_generated_of_le (axioms F a b) T.val h
    rw [T.property] at hg
    exact hg

theorem interpretation_theory_bound (R : FirstOrderPresentation V)
    (f : X ⟶ R.syntaxData.sentenceObject) (a b : Subobject X) (T : R.Theories) :
    (Subobject.«exists» (F.interpretation R f).sentence).obj (theory F a b).val ≤ T.val ↔
      a ≤ (Subobject.pullback f).obj T.val ∧
      b ≤ (Subobject.pullback f).obj
        ((Subobject.pullback R.syntaxData.sentenceNegation).obj T.val) := by
  have hn : (NullaryInterpretation.atomSentence (F.syntaxData X) ≫
      (F.syntaxData X).sentenceNegation) ≫ (F.interpretation R f).sentence =
      f ≫ R.syntaxData.sentenceNegation := by
    calc
      _ = NullaryInterpretation.atomSentence (F.syntaxData X) ≫
          ((F.syntaxData X).sentenceNegation ≫ (F.interpretation R f).sentence) :=
        Category.assoc _ _ _
      _ = NullaryInterpretation.atomSentence (F.syntaxData X) ≫
          ((F.interpretation R f).sentence ≫ R.syntaxData.sentenceNegation) :=
        congrArg (fun k => NullaryInterpretation.atomSentence (F.syntaxData X) ≫ k)
          (F.interpretation R f).sentence_negation
      _ = f ≫ R.syntaxData.sentenceNegation := by
        rw [← Category.assoc, F.interpretation_atom]
  rw [image_theory_le_iff, image_axioms_le_iff, F.interpretation_atom, hn,
    Subobject.pullback_comp]

theorem evaluation_consistent (R : FirstOrderPresentation V) (T : R.Theories)
    (hc : R.Consistent T.val) :
    (F.presentation R.syntaxData.sentenceObject).Consistent
      (theory F T.val ((Subobject.pullback R.syntaxData.sentenceNegation).obj T.val)).val := by
  let τ := F.interpretation R (𝟙 R.syntaxData.sentenceObject)
  have hb : (Subobject.«exists» τ.sentence).obj
      (theory F T.val ((Subobject.pullback R.syntaxData.sentenceNegation).obj T.val)).val ≤
      T.val := by
    apply (interpretation_theory_bound F R (𝟙 _) _ _ T).mpr
    simp only [Subobject.pullback_id, le_refl, and_self]
  have hinv := τ.inverse_consistent T.val hc
  exact FirstOrderPresentation.consistent_of_le _
    ((Subobject.existsPullbackAdj τ.sentence).gc _ _ |>.mp hb) hinv

end CategoricalEssentialIncompleteness.V46.SignedFirstOrder
