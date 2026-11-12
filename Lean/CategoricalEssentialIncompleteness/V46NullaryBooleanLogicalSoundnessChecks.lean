/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanLogicalSoundness

/-! # Statement checks for NullaryBooleanLogicalSoundness -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)
open NullaryBooleanValuation

example : S.logicalAxioms ≫ valuation S d = Two.constant _ true := logical_axioms_value S d
example : S.hilbertInstantiation ≫ valuation S d = Two.constant _ true :=
  hilbert_instantiation_value S d
example : S.hilbertEquality ≫ valuation S d = Two.constant _ true := hilbert_equality_value S d

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.hilbert_one_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.hilbert_two_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.hilbert_three_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.hilbert_instantiation_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.hilbert_distribution_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.hilbert_reflexivity_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.hilbert_equality_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.logical_axioms_value
