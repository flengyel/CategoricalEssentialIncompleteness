/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSubstitutionInvariant

/-! # Statement checks for NullaryBooleanSubstitutionInvariant -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)
open NullaryBooleanValuation

example {A : Over S.substitutionParameters} (m : A ⟶ S.substitutionAlgebra.a.2) :
    m ≫ (invariantMask S d).2 = m ≫ (invariantResult S d).2 ↔
      PairGood S d (m.left ≫ prod.snd) := invariant_equation S d m

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.invariant_equation
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.equality_closed
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.relation_closed
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.negation_closed
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_closed
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.quantifier_closed
