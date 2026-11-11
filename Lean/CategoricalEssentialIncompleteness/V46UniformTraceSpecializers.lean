/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceBuilders

/-! # Actual PA-total programs enumerating specialized program indices -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

/-- The graph is the numerical index builder, not substitution in a
logical formula or in an arithmetized proof. -/
def specializerSectionGraph (e : ℕ) : Graph :=
  let S := specializationGraph
  .mkSigma “a p. !S.val p !!(e) a”

theorem specializerSectionGraph_functional (e : ℕ) :
    𝗣𝗔 ⊢ functionalSentence (specializerSectionGraph e) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, functionalSentence_eval, specializerSectionGraph]

/-- This standard index is selected from the actual functional search
program for a -> specialize(e,a). Its graph is total in PA below. -/
def specializerSectionIndex (e : ℕ) : ℕ := SyntacticSearch.searchIndex (specializerSectionGraph e)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance specializersLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance specializersLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem specializerSectionGraph_model (e : ℕ) (a p : M) :
    (specializerSectionGraph e).val.Evalb ![a, p] ↔ p = specialize (e : M) a := by
  simp [specializerSectionGraph, numeral_eq_natCast_app]

theorem specializerSection_eval (e : ℕ) (a p : M) :
    graph.val.Evalb ![(specializerSectionIndex e : M), a, p] ↔ p = specialize (e : M) a := by
  have hsection := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) (specializerSectionIndex e) a p
  simp only [numeral_eq_natCast_app] at hsection
  have hU := SyntacticSearch.search_uniform_of_functional 𝗣𝗔
    (specializerSectionGraph e) (specializerSectionGraph_functional e)
  have hmodel := consequence_iff.mp (Theory.Proof.sound hU) M inferInstance
  rw [models_iff, uniformSentence_eval] at hmodel
  exact hsection.trans (by
    simpa only [specializerSectionIndex, specializerSectionGraph_model] using hmodel a p)

theorem specializerSection_total (e : ℕ) (a : M) :
    ∃! p : M, graph.val.Evalb ![(specializerSectionIndex e : M), a, p] := by
  simp only [specializerSection_eval]
  refine ⟨specialize (e : M) a, rfl, ?_⟩
  intro p hp
  exact hp

end Models

def specializerSectionSentence (e : ℕ) : ArithmeticSentence :=
  let G := graph
  let S := specializationGraph
  “∀ a p, !G.val !!(specializerSectionIndex e) a p ↔ !S.val p !!(e) a”

theorem specializerSection_PA (e : ℕ) : 𝗣𝗔 ⊢ specializerSectionSentence e := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, specializerSectionSentence, specializerSection_eval, numeral_eq_natCast_app]

def specializerSectionTotalitySentence (e : ℕ) : ArithmeticSentence :=
  let G := graph
  “∀ a, ∃ p, !G.val !!(specializerSectionIndex e) a p ∧
    ∀ q, !G.val !!(specializerSectionIndex e) a q → q = p”

theorem specializerSection_totality_PA (e : ℕ) : 𝗣𝗔 ⊢ specializerSectionTotalitySentence e := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, specializerSectionTotalitySentence, specializerSection_eval,
    numeral_eq_natCast_app]

end CategoricalEssentialIncompleteness.V46.UniformTrace
