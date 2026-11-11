/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInduction


/-! # Statement checks in `V46DerivationStandardInductionChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.DerivationStandardInductionChecks
open SyntacticDerivation SyntacticDerivation.StandardInduction
example {F₀ : PredicateCategory 𝗣𝗔} {bound : ℕ} (R : RulePresentation F₀ bound)
    (P : Obj 𝗣𝗔 ℕ (derivationAlgebra 𝗣𝗔 R).a.left → Prop)
    (step : ∀ (i : Fin (bound + 1)) (r : Obj 𝗣𝗔 ℕ (R.ruleObject (derivationAlgebra 𝗣𝗔 R).a i)),
      (∀ k : Fin i.val, P ((F 𝗣𝗔 ℕ).map (typedChild 𝗣𝗔 R i k) r)) →
        P ((F 𝗣𝗔 ℕ).map (derivationConstructor 𝗣𝗔 R i) r)) :
    ∀ d : Obj 𝗣𝗔 ℕ (derivationAlgebra 𝗣𝗔 R).a.left, P d := nat_rule_induction 𝗣𝗔 R P step
end CategoricalEssentialIncompleteness.V46.DerivationStandardInductionChecks
