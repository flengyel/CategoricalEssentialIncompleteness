/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PrecompleteClasses
public import CategoricalEssentialIncompleteness.V46UniformTraceComparison
public import FailureOfComposition.ConcreteAdequacy
public import FailureOfComposition.UniformIndexQuotient

/-! # Precompleteness of PA-provable program equality

In Bernardi's example in §8.6, the totalizer returns an index. Its
program waits for the given partial function to produce an index, then
runs that index on the remaining input.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.UniformIndexQuotient
open Encodable Denumerable

namespace CategoricalEssentialIncompleteness.V46.ProvableProgramEquality

/-- On the pair of n and x, run e on n and apply its output to x. -/
def applicationGraph (e : ℕ) : Graph :=
  let P := ExponentialPairing.graph
  let G := UniformTrace.graph
  .mkSigma “b y. ∃ n x j, !P.val b n x ∧ !G.val !!(e) n j ∧ !G.val j x y”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance

theorem applicationGraph_eval (e : ℕ) (b y : M) :
    (applicationGraph e).val.Evalb ![b, y] ↔ ∃ n x j : M,
      b = ExponentialPairing.code n x ∧
      UniformTrace.graph.val.Evalb ![(e : M), n, j] ∧
      UniformTrace.graph.val.Evalb ![j, x, y] := by
  simp [applicationGraph, numeral_eq_natCast_app]

theorem applicationGraph_pair (e : ℕ) (n x y : M) :
    (applicationGraph e).val.Evalb ![ExponentialPairing.code n x, y] ↔
      ∃ j : M, UniformTrace.graph.val.Evalb ![(e : M), n, j] ∧
        UniformTrace.graph.val.Evalb ![j, x, y] := by
  rw [applicationGraph_eval]
  constructor
  · rintro ⟨n', x', j, he, hj, hy⟩
    obtain ⟨rfl, rfl⟩ := ExponentialPairing.code_injective he
    exact ⟨j, hj, hy⟩
  · rintro ⟨j, hj, hy⟩
    exact ⟨n, x, j, rfl, hj, hy⟩

private theorem graph_at_index (e : ℕ) (x y : M) :
    UniformTrace.graph.val.Evalb ![(e : M), x, y] ↔ (eventualGraph e).val.Evalb ![x, y] := by
  simpa only [numeral_eq_natCast_app] using canonicalPartrecGraphFormula_eval_iff_eventualGraph e x y

private theorem convergence_in_model {e n j : ℕ} (h : j ∈ Kleene.eval e n) :
    UniformTrace.graph.val.Evalb ![(e : M), (n : M), (j : M)] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗥₀ := models_of_subtheory (U := 𝗣𝗔⁻) inferInstance
  have hstd := (eventualGraph_adequate e n j).mpr h
  have hm := bold_sigma_one_completeness' (M := M) (eventualGraph e).sigma_prop hstd
  rw [numeral_eq_natCast] at hm
  have hv : (Nat.cast ∘ (![n, j] : Fin 2 → ℕ)) = ![(n : M), (j : M)] := by
    funext i
    fin_cases i <;> rfl
  exact (graph_at_index e _ _).mpr (hv ▸ hm)
end Models

theorem applicationGraph_functional (e : ℕ) : 𝗣𝗔 ⊢ functionalSentence (applicationGraph e) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro b y z hy hz
  obtain ⟨n, x, j, he, hj, hy⟩ := (applicationGraph_eval e b y).mp hy
  obtain ⟨n', x', k, he', hk, hz⟩ := (applicationGraph_eval e b z).mp hz
  obtain ⟨rfl, rfl⟩ := ExponentialPairing.code_injective (he.symm.trans he')
  obtain rfl := UniformTrace.output_unique _ _ _ _ hj hk
  exact UniformTrace.output_unique _ _ _ _ hy hz

/-- Ordinary specialization of the fixed search program for the application graph. -/
def totalizer (e n : ℕ) : ℕ :=
  UniformTrace.specialize (SyntacticSearch.searchIndex (applicationGraph e)) n

theorem totalizer_computable (e : ℕ) : Computable (totalizer e) :=
  (UniformTrace.specialize_primrec.comp (Primrec.const _) Primrec.id).to_comp

theorem totalizer_eqIndex {e n j : ℕ} (h : j ∈ Kleene.eval e n) : EqIndex 𝗣𝗔 (totalizer e n) j := by
  let d := SyntacticSearch.searchIndex (applicationGraph e)
  have hd := SyntacticSearch.search_uniform_of_functional 𝗣𝗔 (applicationGraph e)
    (applicationGraph_functional e)
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hs := consequence_iff.mp (Theory.Proof.sound hd) M inferInstance
  rw [models_iff, uniformSentence_eval] at hs ⊢
  intro x y
  change (eventualGraph (UniformTrace.specialize d n)).val.Evalb ![x, y] ↔ _
  rw [← graph_at_index, UniformTrace.specialize_natCast, UniformTrace.specialize_eval, graph_at_index]
  rw [hs, applicationGraph_pair]
  have hj : UniformTrace.graph.val.Evalb ![(e : M), (n : M), (j : M)] := convergence_in_model h
  constructor
  · rintro ⟨k, hk, hy⟩
    obtain rfl := UniformTrace.output_unique _ _ _ _ hj hk
    exact (graph_at_index j x y).mp hy
  · intro hy
    exact ⟨(j : M), hj, (graph_at_index j x y).mpr hy⟩

theorem precomplete : Precomplete (EqIndex 𝗣𝗔) := by
  intro f hf
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨totalizer (encode c), totalizer_computable _, ?_⟩
  intro n j hj
  apply totalizer_eqIndex
  simpa only [Kleene.eval, ofNat_encode, hc] using hj

/-- At every convergent input PA proves uniform equality of the output program and
the program returned by the total recursive function. -/
theorem uniform_totalization (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ n j, j ∈ f n →
      𝗣𝗔 ⊢ uniformSentence (eventualGraph j) (eventualGraph (g n)) := by
  obtain ⟨g, hg, h⟩ := precomplete f hf
  exact ⟨g, hg, fun n j hj => uniform_symm (h n j hj)⟩

end CategoricalEssentialIncompleteness.V46.ProvableProgramEquality
