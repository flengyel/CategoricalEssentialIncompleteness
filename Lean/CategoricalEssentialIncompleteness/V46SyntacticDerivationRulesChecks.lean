/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationRules

/-! The actual arithmetic sources of typed finite-inference summands. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {F Q : PredicateCategory T} {N : ℕ}
variable (R : RulePresentation F N) (q : GraphMorphism T Q F) (i : Fin (N + 1))
example : GraphMorphism T (R.instances i) (tupleCarrier F i.val) := encodedPremises T R i
example : GraphMorphism T (ruleInputCarrier R q i) F := ruleInputConclusion R q i
example :
    representedArrow T (ruleInputLabel R q i) ≫ representedArrow T (encodedPremises T R i) =
      representedArrow T (ruleInputChildren R q i) ≫ representedArrow T (tupleMorphism q i.val) :=
  ruleInput_square R q i
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (r d : M) :
    (ruleInputCarrier R q 0).val.Evalb ![Arithmetic.pair r d] ↔
      (R.instances 0).val.Evalb ![r] ∧ d = 0 :=
  RuleInput.nullary_carrier (encodedPremises T R 0) q M r d
