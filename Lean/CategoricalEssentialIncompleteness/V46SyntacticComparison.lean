/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46Comparison
import CategoricalEssentialIncompleteness.SyntacticFiniteSwitch

/-! # Syntactic inseparability through complementary source conditionals -/

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedTuringMorphism
open FailureOfComposition.TypedRecursionCategory
open PCategoryStruct (nearProd)

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Corollary 6.3 in the coded syntactic presentation, with an arbitrary
chosen Turing morphism and coproduct isomorphism. The model interpretation
and the constructed finite-switch program instantiate Corollary 3.3. -/
theorem syntactic_pair_inseparable_v46_of_model
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (τ : nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T)
    (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : omegaObject T ≅ coprod (omegaObject T) (omegaObject T)) :
    Inseparable (diagonal0 τ b) (diagonal1 τ b) := by
  have hU : (modelRangeFunctor T M).toFunctor.map (𝟙 (omegaObject T)) ≠ 0 := by
    rw [(modelRangeFunctor T M).toFunctor.map_id]
    intro he
    have h := congrFun he (0 : M)
    change Part.some (0 : M) = Part.none at h
    exact Part.notMem_none 0 (h ▸ Part.mem_some 0)
  exact source_inseparable_of_complementary_conditionals (modelRangeFunctor T M)
    τ hτ b hU (fun c c' hc => syntactic_finite_switch T c c' hc)

/-- The model family supplies the nontrivial target whenever the source
theory is consistent. The diagonal data remain arbitrary. -/
theorem syntactic_pair_inseparable_v46 (hT : Consistent T)
    (τ : nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T)
    (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : omegaObject T ≅ coprod (omegaObject T) (omegaObject T)) :
    Inseparable (diagonal0 τ b) (diagonal1 τ b) :=
  source_inseparable_of_complementary_conditionals (familyRangeFunctor T)
    τ hτ b (family_nonzero T hT) (fun c c' hc => syntactic_finite_switch T c c' hc)

/-- The specified syntactic diagonal pair follows through the same
complementary-conditional comparison. -/
theorem syntactic_fixed_pair_inseparable_v46 (hT : Consistent T) :
    Inseparable (syntacticPair0 T) (syntacticPair1 T) :=
  syntactic_pair_inseparable_v46 T hT (typedTau T) (typedTau_isTuringMorphism T)
    (omegaCoprodIso T).symm

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
