/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderTranslationReflection

/-! # Statement checks for reflection across presentations -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.FirstOrderPresentation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}

example (A : Axioms (D := D) V) :
    ((Axioms.generation.obj A).obj).presentation = A.presentation := rfl

example (A : Axioms (D := D) V) :
    ((Axioms.generation.obj A).obj).axioms =
      FirstOrderReflection.generated A.presentation.proofs A.axioms := rfl

example (A : Axioms (D := D) V) (B : Axioms.TheoryCategory (D := D) (V := V)) :
    (Axioms.generation.obj A ⟶ B) ≃ (A ⟶ Axioms.inclusion.obj B) := Axioms.homEquiv A B

example (A : Axioms (D := D) V) (B : Axioms.TheoryCategory (D := D) (V := V))
    (f : Axioms.generation.obj A ⟶ B) :
    (Axioms.homEquiv A B f).translation = f.hom.translation :=
  Axioms.homEquiv_translation A B f

example : Axioms.generation (D := D) (V := V) ⊣ Axioms.inclusion := Axioms.adjunction

example : (Axioms.inclusion (D := D) (V := V)).Full := inferInstance

example : (Axioms.inclusion (D := D) (V := V)).Faithful := inferInstance

#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Axioms.generation
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Axioms.homEquiv
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Axioms.adjunction
