/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorLaws
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxUniqueness

/-! # Actual constructor equations and uniqueness of finite-record evaluation -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

/-- The unguarded whole-word recursion law keeps the actual raw input
and all child/operation witnesses existential. Their positive graph
conditions supply the source guards, including parameter membership. -/
theorem evaluation_iff_root (formula : Bool) (p word value : M) :
    ((A.evaluationFormula formula).val.Evalb ![p, word, value] ↔ ∃ u v : M,
      (constructorGraph formula (if formula then b else a)).val.Evalb ![word, u] ∧
      (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true)
        (if formula then b else a)).val.Evalb ![p, u, v] ∧
      (if formula then A.formulaOp else A.termOp).val.Evalb ![p, v, value]) := by
  constructor
  · intro he
    obtain ⟨hp, hc, _⟩ := A.evaluation_fiber formula p word value he
    obtain ⟨u, hu, hw⟩ := carrier_decomposition formula a b word hc
    rw [hw] at he
    obtain ⟨v, hm, hop⟩ := (A.evaluation_constructor formula p u value hp hu).mp he
    exact ⟨u, v, (constructorGraph_eval formula _ word u).mpr hw, hm, hop⟩
  · rintro ⟨u, v, hc, hm, hop⟩
    have hw := (constructorGraph_eval formula _ word u).mp hc
    rw [hw]
    exact A.evaluation_of_mapRaw formula p u v value hm hop

/-- Every graph candidate obeying the actual constructor equations
agrees with the canonical evaluator on each accepted literal word.
Candidate totality and support are not assumed by this comparison. -/
theorem evaluation_unique (hT hF : TernaryGraph)
    (hroot : A.RootEquations (M := M) hT hF)
    (formula : Bool) (p word x y : M)
    (hx : (if formula then hF else hT).val.Evalb ![p, word, x])
    (hy : (A.evaluationFormula formula).val.Evalb ![p, word, y]) : x = y :=
  A.comparison_of_root_equations hT hF hroot A.evaluation_root_equations formula p word x y hx hy

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
