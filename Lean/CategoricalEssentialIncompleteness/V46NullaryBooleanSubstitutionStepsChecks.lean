/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanSubstitutionSteps

/-! # Statement checks for NullaryBooleanSubstitutionSteps -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)
open NullaryBooleanValuation

example {W : D} (p : W ⟶ S.substitutionParameters) (y : W ⟶ V)
    (a : W ⟶ S.substitutionCarriers.2) (ha : PairGood S d a) :
    PairGood S d (prod.lift p (prod.lift y a) ≫ S.quantifierSubstitutionPair) :=
  quantifier_pair_good S d p y a ha

#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.pairGood_precomp
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.equality_pair_good
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.relation_pair_good
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.negation_pair_good
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.implication_pair_good
#print axioms CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.quantifier_pair_good
