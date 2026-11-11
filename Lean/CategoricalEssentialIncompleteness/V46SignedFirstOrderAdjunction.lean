/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFirstOrderCategories

/-! # The free first-order adjunction on consistent signed pairs -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SignedFirstOrder

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} (F : NullaryPresentations V)

def restrict {A : Pair F} {B : Theories (D := D) (V := V)}
    (h : generatedObject F A ⟶ B) : A ⟶ extractionObject F B := by
  let τ : (F.presentation A.carrier).Translation B.presentation := h.hom.hom.translation
  let a := NullaryInterpretation.atomSentence (F.syntaxData A.carrier) ≫ τ.sentence
  have he := F.interpretation_unique B.presentation a τ rfl
  have hb : (Subobject.«exists» τ.sentence).obj (theory F A.positive A.negative).val ≤
      B.theory.val := h.hom.hom.bound
  rw [he] at hb
  have hp := (interpretation_theory_bound F B.presentation a A.positive A.negative B.theory).mp hb
  exact ⟨a, hp.1, hp.2⟩

def extend {A : Pair F} {B : Theories (D := D) (V := V)}
    (h : A ⟶ extractionObject F B) : generatedObject F A ⟶ B :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨F.interpretation B.presentation h.arrow,
      (interpretation_theory_bound F B.presentation h.arrow A.positive A.negative B.theory).mpr
        ⟨h.positive, h.negative⟩⟩)

def homEquiv (A : Pair F) (B : Theories (D := D) (V := V)) :
    (generatedObject F A ⟶ B) ≃ (A ⟶ extractionObject F B) where
  toFun := restrict F
  invFun := extend F
  left_inv h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply FirstOrderPresentation.Axioms.Hom.ext
    exact (F.interpretation_unique B.presentation _ h.hom.hom.translation rfl).symm
  right_inv h := by
    apply Pair.Hom.ext
    exact F.interpretation_atom B.presentation h.arrow

def adjunction : generation F ⊣ extraction F :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv F
    homEquiv_naturality_left_symm := by
      intro A B T f a
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply FirstOrderPresentation.Axioms.Hom.ext
      symm
      change FirstOrderPresentation.Translation.comp (F.map f.arrow)
          (F.interpretation T.presentation a.arrow) =
        F.interpretation T.presentation (f.arrow ≫ a.arrow)
      apply F.interpretation_unique
      change NullaryInterpretation.atomSentence (F.syntaxData A.carrier) ≫
          ((F.map f.arrow).sentence ≫ (F.interpretation T.presentation a.arrow).sentence) = _
      simp only [NullaryPresentations.map, Category.assoc,
        NullaryPresentations.interpretation_atom_assoc, NullaryPresentations.interpretation_atom]
    homEquiv_naturality_right := by
      intro A B T f g
      apply Pair.Hom.ext
      change NullaryInterpretation.atomSentence (F.syntaxData A.carrier) ≫
          (f.hom.hom.translation.sentence ≫ g.hom.hom.translation.sentence) =
        (NullaryInterpretation.atomSentence (F.syntaxData A.carrier) ≫
          f.hom.hom.translation.sentence) ≫ g.hom.hom.translation.sentence
      exact (Category.assoc _ _ _).symm }

theorem unit_arrow (A : Pair F) :
    ((adjunction F).unit.app A).arrow = NullaryInterpretation.atomSentence (F.syntaxData A.carrier) := by
  change NullaryInterpretation.atomSentence (F.syntaxData A.carrier) ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem counit_translation (A : Theories (D := D) (V := V)) :
    ((adjunction F).counit.app A).hom.hom.translation =
      F.interpretation A.presentation (𝟙 A.presentation.syntaxData.sentenceObject) := rfl

end CategoricalEssentialIncompleteness.V46.SignedFirstOrder
