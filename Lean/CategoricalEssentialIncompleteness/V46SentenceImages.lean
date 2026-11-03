/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46RegularImage
import CategoricalEssentialIncompleteness.V46Inference
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Sentence images and inclusion of generated theories -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D]

/-- The comparison from proofs with sentence conclusions to the sentence
part of the image of all conclusions. -/
def sentenceImageQuotient {P F S : D} (c : P ⟶ F) (j : S ⟶ F) :
    pullback c j ⟶ pullback (image.ι c) j :=
  pullback.map c j (image.ι c) j (factorThruImage c) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

theorem sentenceImageQuotient_isPullback {P F S : D} (c : P ⟶ F) (j : S ⟶ F) :
    IsPullback (sentenceImageQuotient c j) (pullback.fst c j)
      (pullback.fst (image.ι c) j) (factorThruImage c) := by
  have h : IsPullback
      (sentenceImageQuotient c j ≫ pullback.snd (image.ι c) j)
      (pullback.fst c j) j (factorThruImage c ≫ image.ι c) := by
    simpa [sentenceImageQuotient] using (IsPullback.of_hasPullback c j).flip
  exact h.of_right (by simp [sentenceImageQuotient])
    (IsPullback.of_hasPullback (image.ι c) j).flip

instance sentenceImageQuotient_regularEpi {P F S : D} (c : P ⟶ F) (j : S ⟶ F) :
    IsRegularEpi (sentenceImageQuotient c j) := by
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback
    (sentenceImageQuotient_isPullback c j).flip
  change IsRegularEpi (factorThruImage c)
  infer_instance

/-- The regular image of sentence conclusions is the pullback of the
formula image to sentences. -/
def sentenceImageIso {P F S : D} (c : P ⟶ F) (j : S ⟶ F) :
    pullback (image.ι c) j ≅ image (pullback.snd c j) :=
  image.isoStrongEpiMono (sentenceImageQuotient c j) (pullback.snd (image.ι c) j)
    (by simp [sentenceImageQuotient])

@[simp, reassoc] theorem sentenceImageIso_hom_ι {P F S : D} (c : P ⟶ F) (j : S ⟶ F) :
    (sentenceImageIso c j).hom ≫ image.ι (pullback.snd c j) = pullback.snd (image.ι c) j :=
  image.isoStrongEpiMono_hom_comp_ι _ _ _

theorem sentenceImage_subobject {P F S : D} (c : P ⟶ F) (j : S ⟶ F) :
    imageSubobject (pullback.snd c j) = (Subobject.pullback j).obj (imageSubobject c) := by
  change Subobject.mk (image.ι (pullback.snd c j)) =
    (Subobject.pullback j).obj (Subobject.mk (image.ι c))
  rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback (image.ι c) j)]
  exact Subobject.mk_eq_mk_of_comm _ _ (sentenceImageIso c j).symm
    (by simp [sentenceImageIso])

/-- A natural inclusion of inference operations induces inclusion of the
generated images, by initiality of the source derivation algebra. -/
theorem initial_image_monotone {F : D} {H H' : Over F ⥤ Over F}
    (ι : H ⟶ H') (A : Endofunctor.Algebra H) (hA : IsInitial A)
    (A' : Endofunctor.Algebra H') :
    imageSubobject A.a.hom ≤ imageSubobject A'.a.hom := by
  let B : Endofunctor.Algebra H := ⟨A'.a, ι.app A'.a ≫ A'.str⟩
  let f : A ⟶ B := hA.to B
  apply imageSubobject_le _
    (f.f.left ≫ factorThruImageSubobject A'.a.hom)
  rw [Category.assoc, imageSubobject_arrow_comp]
  exact Over.w f.f

/-- Inclusion of typed rule instances gives inclusion of their generated
formula theories. -/
theorem generated_image_monotone [HasFiniteCoproducts D] {F : D} {N : ℕ}
    {R R' : RulePresentation F N} (ι : RulePresentation.Hom R R')
    (A : Endofunctor.Algebra R.inference) (hA : IsInitial A)
    (A' : Endofunctor.Algebra R'.inference) :
    imageSubobject A.a.hom ≤ imageSubobject A'.a.hom :=
  initial_image_monotone ι.inferenceTransformation A hA A'

end CategoricalEssentialIncompleteness.V46
