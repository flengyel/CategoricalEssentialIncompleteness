/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46PartialSearchLift
import CategoricalEssentialIncompleteness.V46SyntacticComparison

/-! # Diagonal comparison with model-disjoint Sigma-one predicates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedTuringMorphism FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

namespace CategoricalEssentialIncompleteness.V46.PartialSearchLift

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The partial search lift supplies the hypothesis of Theorem 3.1 for
the fixed syntactic Turing morphism and its specified diagonal pair. -/
theorem syntactic_partial_comparison (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x]))
    (ha0 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (SyntacticModel.syntacticPair0 𝗣𝗔) ≤ setIdem {x : M | C.val.Evalb ![x]})
    (ha1 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (SyntacticModel.syntacticPair1 𝗣𝗔) ≤ setIdem {x : M | D.val.Evalb ![x]}) :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map g)
        (setIdem {x : M | C.val.Evalb ![x]}) = ⊥ ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map g)
        (setIdem {x : M | D.val.Evalb ![x]}) = ⊥ ∧
      setIdem {x : M | C.val.Evalb ![x]} ⊔ setIdem {x : M | D.val.Evalb ![x]} ≠ ⊤ := by
  let F := SyntacticModel.modelRangeFunctor 𝗣𝗔 M
  let P : Idem (PartialFun.of M) := setIdem {x : M | C.val.Evalb ![x]}
  let N : Idem (PartialFun.of M) := setIdem {x : M | D.val.Evalb ![x]}
  have hPN : P ⊓ N = ⊥ := by
    apply support_injective
    ext x
    simp only [support_inf, support_bot, Set.mem_inter_iff, Set.mem_empty_iff_false]
    exact iff_false_intro (hd x)
  obtain ⟨g, hg, hP, hN⟩ := comparison_zero_inverse_images F
    (typedTau 𝗣𝗔) (typedTau_isTuringMorphism 𝗣𝗔) (omegaCoprodIso 𝗣𝗔).symm
    P N hPN ha0 ha1 ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D))
    (pull_summand0 M C D hd) (pull_summand1 M C D hd) (lift C D)
    (lift_comparison M C D)
  have hU : F.toFunctor.map (𝟙 (omegaObject 𝗣𝗔)) ≠ 0 := by
    rw [F.toFunctor.map_id]
    intro he
    have h := congrFun he (0 : M)
    change Part.some (0 : M) = Part.none at h
    exact Part.notMem_none 0 (h ▸ Part.mem_some 0)
  exact ⟨g, hg, hP, hN, comparison_noncoverage F g hg P N hP hN hU
    (JoinInverse.pull_sup _ P N)⟩

theorem syntactic_predicates_noncoverage (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x]))
    (ha0 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (SyntacticModel.syntacticPair0 𝗣𝗔) ≤ setIdem {x : M | C.val.Evalb ![x]})
    (ha1 : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (SyntacticModel.syntacticPair1 𝗣𝗔) ≤ setIdem {x : M | D.val.Evalb ![x]}) :
    ∃ x : M, ¬C.val.Evalb ![x] ∧ ¬D.val.Evalb ![x] := by
  classical
  obtain ⟨_, _, _, _, hnc⟩ := syntactic_partial_comparison M C D hd ha0 ha1
  by_contra h
  apply hnc
  apply support_injective
  ext x
  simp only [support_sup, support_setIdem, support_top, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  by_cases hC : C.val.Evalb ![x]
  · exact Or.inl hC
  · exact Or.inr (by_contra fun hD => h ⟨x, hC, hD⟩)

end CategoricalEssentialIncompleteness.V46.PartialSearchLift
