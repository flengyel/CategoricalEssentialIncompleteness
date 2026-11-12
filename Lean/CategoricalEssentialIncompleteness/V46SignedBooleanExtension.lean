/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSentenceTheory
public import CategoricalEssentialIncompleteness.V46SignedFirstOrderAdjunction

/-! # A complete extension obtained from a separator -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SignedFirstOrder

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} (F : NullaryPresentations V) {X : D}

def Separates (d : X ⟶ Two D) (a b : Subobject X) : Prop :=
  a.arrow ≫ d = Two.constant _ true ∧ b.arrow ≫ d = Two.constant _ false

def booleanTheory (d : X ⟶ Two D) : (F.presentation X).Theories :=
  ⟨NullaryBooleanValuation.sentenceTheory (F.syntaxData X) d,
    NullaryBooleanValuation.sentence_closed (F.syntaxData X) d (F.proofs X) (F.initial X)⟩

theorem booleanTheory_consistent (d : X ⟶ Two D) :
    (F.presentation X).Consistent (booleanTheory F d).val :=
  NullaryBooleanValuation.sentence_consistent (F.syntaxData X) d

theorem booleanTheory_complete (d : X ⟶ Two D) :
    (booleanTheory F d).val ⊔
      (Subobject.pullback (F.syntaxData X).sentenceNegation).obj (booleanTheory F d).val =
        ⊤ := NullaryBooleanValuation.sentence_complete (F.syntaxData X) d

theorem booleanTheory_contains_axioms (d : X ⟶ Two D) (a b : Subobject X)
    (h : Separates d a b) : axioms F a b ≤ (booleanTheory F d).val := by
  let S := F.syntaxData X
  have hv : NullaryInterpretation.atomSentence S ≫
      NullaryBooleanValuation.sentenceValue S d = d := by
    rw [NullaryBooleanValuation.sentenceValue, ← Category.assoc,
      NullaryInterpretation.atomSentence_inclusion, NullaryBooleanValuation.atom_value]
  have hn : (NullaryInterpretation.atomSentence S ≫ S.sentenceNegation) ≫
      NullaryBooleanValuation.sentenceValue S d = Two.unary Bool.not d := by
    rw [Category.assoc, NullaryBooleanValuation.sentence_negation_value,
      Two.comp_unary, hv]
  dsimp only [axioms]
  apply sup_le
  · apply (Subobject.existsPullbackAdj (NullaryInterpretation.atomSentence S)).gc _ _ |>.mpr
    change a ≤ (Subobject.pullback (NullaryInterpretation.atomSentence S)).obj
      (Two.fiberSubobject (NullaryBooleanValuation.sentenceValue S d) true)
    rw [← Two.fiberSubobject_comp, hv]
    exact (Two.le_fiber_iff a d true).mpr h.1
  · apply (Subobject.existsPullbackAdj
      (NullaryInterpretation.atomSentence S ≫ S.sentenceNegation)).gc _ _ |>.mpr
    change b ≤ (Subobject.pullback (NullaryInterpretation.atomSentence S ≫
      S.sentenceNegation)).obj
      (Two.fiberSubobject (NullaryBooleanValuation.sentenceValue S d) true)
    rw [← Two.fiberSubobject_comp, hn, Two.not_fiber_true]
    exact (Two.le_fiber_iff b d false).mpr h.2

theorem booleanTheory_extends (d : X ⟶ Two D) (a b : Subobject X)
    (h : Separates d a b) : (theory F a b).val ≤ (booleanTheory F d).val :=
  (FirstOrderReflection.generated_le_iff (F.presentation X).proofs
    (F.presentation X).initial (axioms F a b) (booleanTheory F d)).mpr
      (booleanTheory_contains_axioms F d a b h)

end CategoricalEssentialIncompleteness.V46.SignedFirstOrder
