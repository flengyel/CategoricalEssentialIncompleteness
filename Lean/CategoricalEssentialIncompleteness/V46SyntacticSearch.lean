/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.SigmaOneRealization

/-! # Functional search with functionality proved in the ambient theory -/

@[expose] public section

noncomputable section

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition
open FailureOfComposition.ProofSearch FailureOfComposition.ProgramGraph
open FailureOfComposition.SigmaOneRealization FailureOfComposition.SigmaOneSearch
open FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.V46.SyntacticSearch

/-- The selected semidecision program depends only on the graph formula. -/
def semidecisionCode (F : Graph) : PCode :=
  Classical.choose (semidecision_exists F.val F.sigma_prop)

theorem semidecisionCode_spec (F : Graph) : Semidecides F.val (semidecisionCode F) :=
  Classical.choose_spec (semidecision_exists F.val F.sigma_prop)

def searchIndex (F : Graph) : ℕ := Encodable.encode (graphProgram (semidecisionCode F))

/-- The two PA-provable sentences in Lemma 6.2. -/
def soundSentence (e : ℕ) (F : Graph) : ArithmeticSentence :=
  “∀ x y, !(eventualGraph e).val x y → !F.val x y”

def domainSentence (e : ℕ) (F : Graph) : ArithmeticSentence :=
  “∀ x, (∃ y, !(eventualGraph e).val x y) ↔ (∃ y, !F.val x y)”

@[simp] theorem soundSentence_eval {M : Type} [ORingStructure M] (e : ℕ) (F : Graph) :
    (soundSentence e F).Evalb (M := M) ![] ↔
      ∀ x y : M, (eventualGraph e).val.Evalb ![x, y] → F.val.Evalb ![x, y] := by
  simp [soundSentence]

@[simp] theorem domainSentence_eval {M : Type} [ORingStructure M] (e : ℕ) (F : Graph) :
    (domainSentence e F).Evalb (M := M) ![] ↔
      ∀ x : M, (∃ y : M, (eventualGraph e).val.Evalb ![x, y]) ↔
        ∃ y : M, F.val.Evalb ![x, y] := by
  simp [domainSentence]

section Models

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem accepts_iff (F : Graph) (x y : M) :
    Computes (reorderProgram (semidecisionCode F)) (pair y x) 0 ↔
      F.val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  rw [computes_reorder, semidecisionCode_spec F M ![x, y] 0]
  simp

theorem search_sound_in_model (F : Graph) (x y : M)
    (h : (eventualGraph (searchIndex F)).val.Evalb ![x, y]) : F.val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  have hs : Computes (graphProgram (semidecisionCode F)) x y := h
  exact (accepts_iff F x y).mp (candidateSearch_sound _ x y hs)

theorem search_domain_in_model (F : Graph) (x : M) :
    (∃ y : M, (eventualGraph (searchIndex F)).val.Evalb ![x, y]) ↔
      ∃ y : M, F.val.Evalb ![x, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  change (∃ y : M, Computes (graphProgram (semidecisionCode F)) x y) ↔ _
  rw [graphProgram, candidateSearch_domain]
  exact exists_congr (fun y => accepts_iff F x y)

end Models

theorem search_sound (F : Graph) : 𝗣𝗔 ⊢ soundSentence (searchIndex F) F := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, soundSentence_eval]
  exact search_sound_in_model F

theorem search_domain (F : Graph) : 𝗣𝗔 ⊢ domainSentence (searchIndex F) F := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, domainSentence_eval]
  exact search_domain_in_model F

/-- Functionality is required in T. No PA proof of functionality is used. -/
theorem search_uniform_of_functional (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (F : Graph) (hF : T ⊢ functionalSentence F) :
    Uniform T (eventualGraph (searchIndex F)) F := by
  apply complete.{0} T
  intro M _ hM
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hf : M↓[ℒₒᵣ] ⊧ functionalSentence F :=
    consequence_iff.mp (Theory.Proof.sound hF) M hM
  rw [models_iff, functionalSentence_eval] at hf
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · exact search_sound_in_model F x y
  · intro hy
    obtain ⟨z, hz⟩ := (search_domain_in_model F x).mpr ⟨y, hy⟩
    have hzy := hf x z y (search_sound_in_model F x z hz) hy
    simpa only [hzy] using hz

/-- Lemma 6.2 in the fixed production graph presentation. The chosen index and its two PA
proofs are independent of the ambient extension T. -/
theorem functional_search (F : Graph) :
    ∃ e : ℕ, (𝗣𝗔 ⊢ soundSentence e F) ∧ (𝗣𝗔 ⊢ domainSentence e F) ∧
      ∀ (T : ArithmeticTheory) [𝗣𝗔 ⪯ T],
        (T ⊢ functionalSentence F) → Uniform T (eventualGraph e) F :=
  ⟨searchIndex F, search_sound F, search_domain F,
    fun T _ hF => search_uniform_of_functional T F hF⟩

end CategoricalEssentialIncompleteness.V46.SyntacticSearch
