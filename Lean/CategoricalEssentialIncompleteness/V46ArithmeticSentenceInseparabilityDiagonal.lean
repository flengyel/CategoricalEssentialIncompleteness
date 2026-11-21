/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityConditional
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring

/-! # The categorical obstruction to a recursive diagonal separator -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FailureOfComposition FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability

private theorem standard_nonzero :
    (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map (𝟙 (omegaObject 𝗣𝗔)) ≠ 0 := by
  have hid : (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map (𝟙 (omegaObject 𝗣𝗔)) =
      𝟙 (PartialFun.of ℕ) := (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map_id _
  intro he
  have h := congrFun (hid.symm.trans he) (0 : ℕ)
  change Part.some (0 : ℕ) = Part.none at h
  exact Part.notMem_none 0 (h ▸ Part.mem_some 0)

/-- Corollary 3.2 rules out a recursive standard separator of the source diagonal domains.
The source lift is the indexed partial morphism constructed from the recursive
reversed conditional. -/
theorem diagonal_no_recursive_separator :
    ¬ ∃ C : Set ℕ, ComputablePred (· ∈ C) ∧
      {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} ⊆ C ∧
      Disjoint C {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} := by
  rintro ⟨C,hC,hAlpha,hBeta⟩
  let P : Idem (PartialFun.of ℕ) := setIdem C
  let N : Idem (PartialFun.of ℕ) := setIdem Cᶜ
  have hPN : Complementary P N := by
    constructor
    · apply support_injective
      rw [support_inf,support_setIdem,support_setIdem,support_bot]
      exact Set.inter_compl_self C
    · apply support_injective
      rw [support_sup,support_setIdem,support_setIdem,support_top]
      exact Set.union_compl_self C
  have ha0 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).mapIdem ArithmeticDiagonalCodes.a0 ≤ P := by
    rw [ArithmeticDiagonalCodes.model_a0]
    apply (le_iff_support _ _).mpr
    rw [support_setIdem,support_setIdem]
    exact hAlpha
  have ha1 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).mapIdem ArithmeticDiagonalCodes.a1 ≤ N := by
    rw [ArithmeticDiagonalCodes.model_a1]
    apply (le_iff_support _ _).mpr
    rw [support_setIdem,support_setIdem]
    intro n hn hnC
    exact Set.disjoint_left.mp hBeta hnC hn
  obtain ⟨s,q,_,hs0,hs1,hq⟩ := recursive_set_conditional C hC
  exact no_lifted_complementary_separator
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ)
    ArithmeticDiagonalCodes.sourceTau ArithmeticDiagonalCodes.sourceTau_isTuring
    (omegaCoprodIso 𝗣𝗔).symm standard_nonzero P N hPN ha0 ha1
    ⟨s,arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) q,hs0,hs1,hq⟩


end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability
