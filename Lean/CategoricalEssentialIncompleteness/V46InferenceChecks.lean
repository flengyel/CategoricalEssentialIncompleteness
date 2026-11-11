/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Inference


/-! # Statement checks in `V46InferenceChecks` -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoricalEssentialIncompleteness.V46.StatementChecks

variable {D : Type u} [Category.{v} D] [Regular D]

example (X : D) : finitePower X 0 = ⊤_ D := rfl
example (X : D) : finitePower X 1 = X := rfl
example (X : D) : finitePower X 2 = (X ⨯ X) := rfl

example [HasFiniteCoproducts D] {F : D} {N : ℕ} (R : RulePresentation F N)
    (A : Endofunctor.Algebra R.inference) (hA : IsInitial A) :
    Nonempty (R.inference.obj (Over.mk (image.ι A.a.hom)) ⟶
      Over.mk (image.ι A.a.hom)) ∧
      ∀ {U : D} (m : U ⟶ F) [Mono m],
        Nonempty (R.inference.obj (Over.mk m) ⟶ Over.mk m) →
          ∃ w : image A.a.hom ⟶ U, w ≫ m = image.ι A.a.hom :=
  R.least_theorem_subobject A hA

end CategoricalEssentialIncompleteness.V46.StatementChecks
