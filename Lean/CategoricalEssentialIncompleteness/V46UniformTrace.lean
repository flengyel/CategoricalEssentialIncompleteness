/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSearch
import CategoricalEssentialIncompleteness.V46ExponentialPairing
import FailureOfComposition.FirstSuccessGraph

/-! # A uniform functional computation graph and its universal section -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.ArithmeticCode
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

/-- The program index remains an arithmetic variable. -/
abbrev graph : 𝚺₁.Semisentence 3 := canonicalPartrecGraphFormula

/-- The universal program receives the manuscript's exponential pair code. -/
def universalGraph : Graph :=
  let E := ExponentialPairing.graph
  let G := graph
  .mkSigma “input y. ∃ e x, !E.val input e x ∧ !G.val e x y”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem output_unique (e x y z : M)
    (hy : graph.val.Evalb ![e, x, y]) (hz : graph.val.Evalb ![e, x, z]) : y = z := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  exact eval_unique ((canonicalPartrecGraphFormula_eval_iff e x y).mp hy)
    ((canonicalPartrecGraphFormula_eval_iff e x z).mp hz)

@[simp] theorem universalGraph_eval (input y : M) :
    universalGraph.val.Evalb ![input, y] ↔
      ∃ e x : M, input = ExponentialPairing.code e x ∧ graph.val.Evalb ![e, x, y] := by
  simp [universalGraph]

theorem universalGraph_code (e x y : M) :
    universalGraph.val.Evalb ![ExponentialPairing.code e x, y] ↔
      graph.val.Evalb ![e, x, y] := by
  rw [universalGraph_eval]
  constructor
  · rintro ⟨f, a, he, hfa⟩
    obtain ⟨rfl, rfl⟩ := ExponentialPairing.code_injective he
    exact hfa
  · intro h
    exact ⟨e, x, rfl, h⟩

end Models

def functionalitySentence : ArithmeticSentence :=
  let G := graph
  “∀ e x y z, !G.val e x y → !G.val e x z → y = z”

/-- Functionality is uniform in all internal program indices. -/
theorem functionality_PA : 𝗣𝗔 ⊢ functionalitySentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff, functionalitySentence] using (output_unique (M := M))

theorem universalGraph_functional : 𝗣𝗔 ⊢ functionalSentence universalGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro input y z hy hz
  obtain ⟨e, x, he, hy⟩ := (universalGraph_eval input y).mp hy
  obtain ⟨f, a, hf, hz⟩ := (universalGraph_eval input z).mp hz
  obtain ⟨rfl, rfl⟩ := ExponentialPairing.code_injective (he.symm.trans hf)
  exact output_unique e x y z hy hz

def universalIndex : ℕ := SyntacticSearch.searchIndex universalGraph

theorem universalIndex_uniform :
    Uniform 𝗣𝗔 (eventualGraph universalIndex) universalGraph :=
  SyntacticSearch.search_uniform_of_functional 𝗣𝗔 universalGraph universalGraph_functional

def sectionSentence (e : ℕ) : ArithmeticSentence :=
  let G := graph
  let E := eventualGraph e
  “∀ x y, !G.val !!(e) x y ↔ !E.val x y”

/-- At every external index the same PA graph agrees with the production
stage presentation at all internal inputs and outputs. -/
theorem section_PA (e : ℕ) : 𝗣𝗔 ⊢ sectionSentence e := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff, sectionSentence, numeral_eq_natCast_app] using
    (canonicalPartrecGraphFormula_eval_iff_eventualGraph (M := M) e)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The universal graph equation quantifies over arbitrary, including
nonstandard, program indices in the arithmetic model. -/
theorem universal_eval (e x y : M) :
    graph.val.Evalb ![(universalIndex : M), ExponentialPairing.code e x, y] ↔
      graph.val.Evalb ![e, x, y] := by
  have hu := consequence_iff.mp (Theory.Proof.sound universalIndex_uniform) M inferInstance
  rw [models_iff, uniformSentence_eval] at hu
  have hs := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) universalIndex (ExponentialPairing.code e x) y
  simp only [numeral_eq_natCast_app] at hs
  exact hs.trans ((hu _ _).trans (universalGraph_code e x y))

end Models

def universalSentence : ArithmeticSentence :=
  let G := graph
  let E := ExponentialPairing.graph
  “∀ e x z y, !E.val z e x →
    (!G.val !!(universalIndex) z y ↔ !G.val e x y)”

theorem universal_PA : 𝗣𝗔 ⊢ universalSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have h : ∀ e x z y : M, z = ExponentialPairing.code e x →
      (graph.val.Evalb ![(universalIndex : M), z, y] ↔ graph.val.Evalb ![e, x, y]) := by
    intro e x z y he
    subst z
    exact universal_eval e x y
  simpa [models_iff, universalSentence, numeral_eq_natCast_app] using h

end CategoricalEssentialIncompleteness.V46.UniformTrace
