/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSubstitution

/-! # Statement checks for NullaryBooleanSubstitution -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)
open NullaryBooleanValuation

example : S.substitutionFold ≫ invariantMask S d =
    S.substitutionFold ≫ invariantResult S d := fold_invariant S d
example : S.formulaSubstitution ≫ valuation S d =
    S.admissibleInclusion ≫ prod.fst ≫ valuation S d := substitution_value S d

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.constructor_closed
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.fold_invariant
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.substitution_option_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.substitution_value
