/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanValuation

/-! # Statement checks for NullaryBooleanValuation -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)
open NullaryBooleanValuation

example : S.equalityConstructor ≫ valuation S d = Two.constant _ true := equality_value S d
example : NullaryInterpretation.atomFormula S ≫ valuation S d = d := atom_value S d
example : S.negationConstructor ≫ valuation S d = Two.unary Bool.not (valuation S d) :=
  negation_value S d
example : S.quantifierConstructor ≫ valuation S d = prod.snd ≫ valuation S d :=
  quantifier_value S d

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.valuation
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.equality_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.atom_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.negation_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.quantifier_value
