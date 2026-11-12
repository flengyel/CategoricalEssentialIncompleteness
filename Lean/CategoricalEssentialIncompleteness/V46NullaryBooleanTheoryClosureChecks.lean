/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanTheoryClosure

/-! # Statement checks for NullaryBooleanTheoryClosure -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)
open NullaryBooleanValuation

example {A : D} (a : A ⟶ S.sentenceObject)
    (ha : a ≫ S.sentenceInclusion ≫ valuation S d = Two.constant A true) :
    ClosedUnder (S.logicalRules a).inference (trueInclusion S d) := truth_closed S d a ha

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.modus_ponens
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.rule_value
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.truthAlgebra
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.truth_closed
