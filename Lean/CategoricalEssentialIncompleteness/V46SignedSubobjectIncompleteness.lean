/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedBooleanExtension
public import CategoricalEssentialIncompleteness.V46SubobjectInseparability

/-! # Essential incompleteness and inseparability of subobjects -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}

namespace FirstOrderPresentation

def Complete (P : FirstOrderPresentation V) (T : Subobject P.syntaxData.sentenceObject) : Prop :=
  T ⊔ (Subobject.pullback P.syntaxData.sentenceNegation).obj T = ⊤

def EssentiallyIncomplete (P : FirstOrderPresentation V) (T : P.Theories) : Prop :=
  P.Consistent T.val ∧
    ∀ U : P.Theories, T.val ≤ U.val → P.Consistent U.val → ¬ P.Complete U.val

end FirstOrderPresentation

namespace SignedFirstOrder

variable (F : NullaryPresentations V) {X : D} (a b : Subobject X)

theorem essential_incomplete_of_subobject_inseparable
    (h : SubobjectInseparable a b) (hcT : (F.presentation X).Consistent (theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (theory F a b) := by
  refine ⟨hcT, ?_⟩
  intro U hU hc hcomp
  have hb := atomic_bounds F a b
  have hp : a ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).obj
      U.val := hb.1.trans
        ((Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).monotone hU)
  have hn : b ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).obj
      ((Subobject.pullback (F.syntaxData X).sentenceNegation).obj U.val) :=
    hb.2.trans ((Subobject.pullback (NullaryInterpretation.atomSentence (F.syntaxData X))).monotone
      ((Subobject.pullback (F.syntaxData X).sentenceNegation).monotone hU))
  have hs : HasSubobjectSeparator U.val
      ((Subobject.pullback (F.syntaxData X).sentenceNegation).obj U.val) :=
    ⟨⟨U.val, (Subobject.pullback (F.syntaxData X).sentenceNegation).obj U.val,
      ⟨disjoint_iff.mpr hc, codisjoint_iff.mpr hcomp⟩⟩, le_rfl, le_rfl⟩
  exact h.2 (subobject_separator_mono hp hn
    (subobject_separator_pullback (NullaryInterpretation.atomSentence (F.syntaxData X)) hs))

theorem no_subobject_separator_of_essential_incomplete
    (h : (F.presentation X).EssentiallyIncomplete (theory F a b)) :
    ¬ HasSubobjectSeparator a b := by
  intro hs
  obtain ⟨d, hd⟩ := (subobject_separator_iff_boolean a b).mp hs
  exact h.2 (booleanTheory F d) (booleanTheory_extends F d a b hd)
    (booleanTheory_consistent F d) (booleanTheory_complete F d)

theorem essential_incomplete_iff_subobject_inseparable
    (hab : a ⊓ b = ⊥) (hcT : (F.presentation X).Consistent (theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (theory F a b) ↔ SubobjectInseparable a b :=
  ⟨fun h => ⟨hab, no_subobject_separator_of_essential_incomplete F a b h⟩,
    fun h => essential_incomplete_of_subobject_inseparable F a b h hcT⟩

end SignedFirstOrder
end CategoricalEssentialIncompleteness.V46
