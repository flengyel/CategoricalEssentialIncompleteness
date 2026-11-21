/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInductionRank


/-! # The original typed rule constructors and their tree-word charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.DerivationStandardInductionRankChecks
open SyntacticDerivation SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F₀ : PredicateCategory T} {bound : ℕ}
  (R : RulePresentation F₀ bound)
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (i : Fin (bound + 1)) (r : Obj T M (R.ruleObject (derivationAlgebra T R).a i)) (k : Fin i.val) :
    len ((F T M).map (typedChild T R i k) r).val <
      len ((F T M).map (derivationConstructor T R i) r).val := typed_children_smaller T R M i r k
end CategoricalEssentialIncompleteness.V46.DerivationStandardInductionRankChecks
