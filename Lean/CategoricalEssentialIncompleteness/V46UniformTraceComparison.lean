/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveBuilders

/-! # Graphs of the two composition indices

Sigma-one completeness is used only to interpret a closed index function value at
standard numerals. Equality of program graphs then follows from the all-model
relational composition equations on both sides.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open CategoricalRiceShapiro.PartialRecursive

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance comparisonLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance comparisonLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance comparisonLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

theorem compose_natCast (f e : ℕ) : ((compose f e : ℕ) : M) = compose (f : M) (e : M) := by
  have hnat : compositionGraph.val.Evalb (M := ℕ) ![compose f e, f, e] :=
    (compositionGraph_eval _ _ _).mpr rfl
  have hmodel := bold_sigma_one_completeness' (M := M) compositionGraph.sigma_prop hnat
  rw [numeral_eq_natCast] at hmodel
  have hv : (Nat.cast ∘ (![compose f e, f, e] : Fin 3 → ℕ)) =
      ![((compose f e : ℕ) : M), (f : M), (e : M)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hmodel
  exact (compositionGraph_eval _ _ _).mp hmodel

theorem specialize_natCast (e a : ℕ) : ((specialize e a : ℕ) : M) = specialize (e : M) (a : M) := by
  have hnat : specializationGraph.val.Evalb (M := ℕ) ![specialize e a, e, a] :=
    (specializationGraph_eval _ _ _).mpr rfl
  have hmodel := bold_sigma_one_completeness' (M := M) specializationGraph.sigma_prop hnat
  rw [numeral_eq_natCast] at hmodel
  have hv : (Nat.cast ∘ (![specialize e a, e, a] : Fin 3 → ℕ)) =
      ![((specialize e a : ℕ) : M), (e : M), (a : M)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hmodel
  exact (specializationGraph_eval _ _ _).mp hmodel

/-- The indices `compose f e` and `canonicalPartrecCompIndex f e` define the same
binary relation in every model of PA. -/
theorem compose_production_model (f e : ℕ) (input output : M) :
    (eventualGraph (compose f e)).val.Evalb ![input, output] ↔
      (eventualGraph (canonicalPartrecCompIndex f e)).val.Evalb ![input, output] := by
  have hNew := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) (compose f e) input output
  have hF := fun (x y : M) => canonicalPartrecGraphFormula_eval_iff_eventualGraph (M := M) f x y
  have hE := fun (x y : M) => canonicalPartrecGraphFormula_eval_iff_eventualGraph (M := M) e x y
  simp only [numeral_eq_natCast_app] at hNew hF hE
  rw [← hNew, compose_natCast, compose_eval, eventualGraph_comp_eval]
  exact exists_congr fun middle => and_congr (hE input middle) (hF middle output)

end Models

theorem compose_production_PA (f e : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (compose f e)) (eventualGraph (canonicalPartrecCompIndex f e)) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  exact compose_production_model f e

end CategoricalEssentialIncompleteness.V46.UniformTrace
