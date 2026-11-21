/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionPullbacks

/-! Every predicate object has the constructed finite option-success pullback. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : PredicateCategory T) (n : ℕ)
example : IsPullback (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n)
    (𝟙 (finitePower Q n)) (OptionPowers.collect Q n)
    (coprod.inr : finitePower Q n ⟶ OptionSyntax.obj (finitePower Q n)) :=
  OptionPullbacks.collect T Q n
