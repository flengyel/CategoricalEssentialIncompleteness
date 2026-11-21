/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionModels


/-! # The distribution parameter fiber in every arithmetic model -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionModels.Checks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
  (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
  (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "Y" => (Postfix.plainCarrier true
  (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) : PredicateCategory T)
example (q : Obj T M (V ⨯ (Y ⨯ Y))) :
    (∃ r : Obj T M (S).distributionParameters,
      (F T M).map (S).distributionInclusion r = q) ↔
      ConcreteNamedSubstitution.member
        ((F T M).map (prod.fst (C := PredicateCategory T) : V ⨯ (Y ⨯ Y) ⟶ V) q).val
        (ConcreteNamedSubstitution.freeVariables (M := M) V σ π d
          ((F T M).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y))
            ((F T M).map (prod.snd (C := PredicateCategory T) : V ⨯ (Y ⨯ Y) ⟶ Y ⨯ Y) q)).val) = 0 :=
  parameter_image_iff T V σ π d M q
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionModels.Checks
