/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SentenceImages


/-! # Statement checks in `V46SentenceImagesChecks` -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoricalEssentialIncompleteness.V46.StatementChecks

variable {D : Type u} [Category.{v} D] [Regular D]

example {P F S : D} (c : P ⟶ F) (j : S ⟶ F) [Mono j] :
    pullback (image.ι c) j ≅ image (pullback.snd c j) :=
  sentenceImageIso c j

example {P F S : D} (c : P ⟶ F) (j : S ⟶ F) [Mono j] :
    imageSubobject (pullback.snd c j) = (Subobject.pullback j).obj (imageSubobject c) :=
  sentenceImage_subobject c j

example {F : D} {H H' : Over F ⥤ Over F}
    (ι : H ⟶ H') (A : Endofunctor.Algebra H) (hA : IsInitial A)
    (A' : Endofunctor.Algebra H') :
    imageSubobject A.a.hom ≤ imageSubobject A'.a.hom :=
  initial_image_monotone ι A hA A'

example [HasFiniteCoproducts D] {F : D} {N : ℕ}
    {R R' : RulePresentation F N} (ι : RulePresentation.Hom R R')
    (A : Endofunctor.Algebra R.inference) (hA : IsInitial A)
    (A' : Endofunctor.Algebra R'.inference) :
    imageSubobject A.a.hom ≤ imageSubobject A'.a.hom :=
  generated_image_monotone ι A hA A'

end CategoricalEssentialIncompleteness.V46.StatementChecks
