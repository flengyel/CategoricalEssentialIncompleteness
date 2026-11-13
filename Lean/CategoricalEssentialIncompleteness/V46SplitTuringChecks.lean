/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitTuring

/-! # Turing morphisms and total embeddings for arbitrary split objects -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory PCategoryStruct RecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness SplitObject
open CategoricalEssentialIncompleteness.V46.SplitTuring

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]

attribute [local instance] productData productLaws

example {W : R} (X Y : SplitObject R) (τ : nearProd W X.base ⟶ Y.base)
    (hτ : IsTuringMorphism τ) (V : SplitObject R)
    (φ : nearProd V X ⟶ Y) :
    ∃ g : V ⟶ (splittingInclusion (C := R)).obj W,
      @PCategoryStruct.rst (SplitObject R) inferInstance productData V
        ((splittingInclusion (C := R)).obj W) g = 𝟙 V ∧
      nearProd_map g (𝟙 X) ≫ evaluator X Y τ = φ :=
  evaluator_isTuring X Y τ hτ V φ

example [Isotype R] (Q : R) (X : SplitObject R) :
    ∃ (m : X ⟶ (splittingInclusion (C := R)).obj Q)
      (r : (splittingInclusion (C := R)).obj Q ⟶ X),
      isTotal m ∧ m ≫ r = 𝟙 X := exists_total_retract Q X

example [CategoryTheory.Limits.HasZeroMorphisms R] [Prodominical R] [Isotype R]
    (T : PRecursionCategory R) :
    ∃ (Q : SplitObject R) (τ : nearProd Q Q ⟶ Q),
      IsTuringMorphism τ ∧
      ∀ X : SplitObject R, ∃ (m : X ⟶ Q) (r : Q ⟶ X),
        isTotal m ∧ m ≫ r = 𝟙 X := turing_object T

#print axioms CategoricalEssentialIncompleteness.V46.SplitTuring.retype
#print axioms CategoricalEssentialIncompleteness.V46.SplitTuring.evaluator_isTuring
#print axioms CategoricalEssentialIncompleteness.V46.SplitTuring.parameter_total
#print axioms CategoricalEssentialIncompleteness.V46.SplitTuring.exists_total_retract
#print axioms CategoricalEssentialIncompleteness.V46.SplitTuring.turingFamily
#print axioms CategoricalEssentialIncompleteness.V46.SplitTuring.turing_object
