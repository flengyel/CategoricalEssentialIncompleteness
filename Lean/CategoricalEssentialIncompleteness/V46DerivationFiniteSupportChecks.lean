/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationFiniteSupport
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInitial

/-! # Finite leaf lists on the constructed arithmetic proof object -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DerivationFiniteSupport.Checks

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {Fm X : SyntacticPredicates.PredicateCategory T} (R : RulePresentation Fm 2)
variable (L : StableListAlgebra X) (leaf : R.instances 0 ⟶ L.algebra.carrier)

example : (SyntacticDerivation.derivationAlgebra T R).a.left ⟶ L.algebra.carrier :=
  collect R L (SyntacticDerivation.derivationAlgebra T R)
    (SyntacticDerivation.derivationInitial T R) leaf

example :
    ruleConstructor R (SyntacticDerivation.derivationAlgebra T R) 0 ≫
      collect R L (SyntacticDerivation.derivationAlgebra T R)
        (SyntacticDerivation.derivationInitial T R) leaf = pullback.fst _ _ ≫ leaf :=
  nullary_collect R L (SyntacticDerivation.derivationAlgebra T R)
    (SyntacticDerivation.derivationInitial T R) leaf

#print axioms constructor_collect
#print axioms nullary_collect
#print axioms unary_collect
#print axioms binary_collect

end CategoricalEssentialIncompleteness.V46.DerivationFiniteSupport.Checks
