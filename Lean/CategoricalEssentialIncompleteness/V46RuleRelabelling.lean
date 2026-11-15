/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46InferenceTranslation

/-! # Relabelling finite inference rules by isomorphisms -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.RuleRelabelling
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {F : D} {N : ℕ} (R : RulePresentation F N)
variable (labels : Fin (N + 1) → D) (e : ∀ i, labels i ≅ R.instances i)

def rules : RulePresentation F N where
  instances := labels
  premises i := (e i).hom ≫ R.premises i
  conclusion i := (e i).hom ≫ R.conclusion i

def forward : (rules R labels e).Translation R where
  formula := 𝟙 F
  map i := (e i).hom
  premises i := by simp [rules]
  conclusion i := by simp [rules]

def backward : R.Translation (rules R labels e) where
  formula := 𝟙 F
  map i := (e i).inv
  premises i := by simp [rules]
  conclusion i := by simp [rules]

theorem conclusion_image_eq
    (P : Endofunctor.Algebra (rules R labels e).inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R.inference) (hQ : IsInitial Q) :
    imageSubobject P.a.hom = imageSubobject Q.a.hom := by
  apply le_antisymm
  · simpa only [forward, Category.comp_id] using (forward R labels e).image_le P hP Q
  · simpa only [backward, Category.comp_id] using (backward R labels e).image_le Q hQ P

theorem sentence_image_eq {S : D} (sentence : S ⟶ F)
    (P : Endofunctor.Algebra (rules R labels e).inference) (hP : IsInitial P)
    (Q : Endofunctor.Algebra R.inference) (hQ : IsInitial Q) :
    imageSubobject (pullback.snd P.a.hom sentence) =
      imageSubobject (pullback.snd Q.a.hom sentence) := by
  apply le_antisymm
  · simpa only [Category.comp_id] using (forward R labels e).sentenceImage_le
      sentence sentence (𝟙 S) (by simp [forward]) P hP Q
  · simpa only [Category.comp_id] using (backward R labels e).sentenceImage_le
      sentence sentence (𝟙 S) (by simp [backward]) Q hQ P

end CategoricalEssentialIncompleteness.V46.RuleRelabelling
