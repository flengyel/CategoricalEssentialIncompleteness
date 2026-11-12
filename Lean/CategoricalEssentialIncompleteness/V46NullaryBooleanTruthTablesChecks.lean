/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanTruthTables

/-! # Statement checks for NullaryBooleanTruthTables -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
open NullaryBooleanValuation
example {W : D} (a b c : W ⟶ Two D) :
    Two.binary implies (Two.binary implies a (Two.binary implies b c))
      (Two.binary implies (Two.binary implies a b) (Two.binary implies a c)) =
        Two.constant W true := implication_two a b c

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_self
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_true_left
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_one
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_two
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_three
