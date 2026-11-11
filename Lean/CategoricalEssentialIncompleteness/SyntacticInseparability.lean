/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticModel
public import CategoricalEssentialIncompleteness.ChoiceSectionLifting

/-! # Categorical inseparability in the uniform syntactic recursion category -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open FailureOfComposition.TypedRecursionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The fixed diagonal pair in the syntactic recursion category. -/
def syntacticPair0 : Idem (omegaObject T) := diagonal0 (typedTau T) (omegaCoprodIso T).symm

def syntacticPair1 : Idem (omegaObject T) := diagonal1 (typedTau T) (omegaCoprodIso T).symm

theorem syntactic_inseparable_of_model (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] :
    Inseparable (syntacticPair0 T) (syntacticPair1 T) := by
  have hU : (rangeFunctor T M).toFunctor.map (𝟙 (omegaObject T)) ≠ 0 := by
    rw [(rangeFunctor T M).toFunctor.map_id]
    intro h
    let x : carrier M .omega :=
      ⟨0, FailureOfComposition.CodedObjectMembership.memberFormula_omega_eval 0⟩
    have he := congrFun h x
    change Part.some x = Part.none at he
    have hx : x ∈ (Part.none : Part (carrier M .omega)) := he ▸ Part.mem_some x
    exact Part.notMem_none x hx
  exact range_functor_lifting (rangeFunctor T M) (typedTau T) (typedTau_isTuringMorphism T)
    (omegaCoprodIso T).symm hU (section_lifting_of_choice (rangeFunctor T M) (omegaObject T))

/-- The existence of a model is needed only through consistency. No
soundness or Sigma-one soundness hypothesis is imposed on `T`. This proof
instantiates the range-functor lifting theorem. -/
theorem syntactic_inseparable (hT : Consistent T) :
    Inseparable (syntacticPair0 T) (syntacticPair1 T) := by
  classical
  by_contra h
  have hf : T ⊢ (⊥ : ArithmeticSentence) := by
    apply Arithmetic.complete.{0} T
    intro M _ _
    exact False.elim (h (syntactic_inseparable_of_model T M))
  exact (consistent_iff_unprovable_bot.mp hT) hf

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
