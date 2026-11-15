/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationInternalInduction

/-! # Rule induction without a standard-model hypothesis -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.InternalInduction.Checks

open StandardInduction

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    {Fm : PredicateCategory T} {bound : ℕ} (R : RulePresentation Fm bound)
    (φ : 𝚷₁.Semiformula M 1)
    (step : ∀ (i : Fin (bound + 1))
      (r : Obj T M (R.ruleObject (derivationAlgebra T R).a i)),
      (∀ k : Fin i.val,
        φ.val.Eval ![((F T M).map (typedChild T R i k) r).val] id) →
      φ.val.Eval ![((F T M).map (derivationConstructor T R i) r).val] id) :
    ∀ d : Obj T M (derivationAlgebra T R).a.left, φ.val.Eval ![d.val] id :=
  model_rule_induction T M R φ step

#print axioms model_rule_induction

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.InternalInduction.Checks
