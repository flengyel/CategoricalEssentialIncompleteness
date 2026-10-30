/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.SigmaOneRealization
import Foundation.FirstOrder.Arithmetic.Schemata

/-! # The finite two-test switch

Search increasing computation bounds for the two zero-valued semidecision
programs.  At the first successful bound the first test has priority.  The
tests inspect finite computation certificates, including in nonstandard PA
models.  All correctness statements below are proved uniformly in those models.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open Nat.ArithPart₁
open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator
open FailureOfComposition FailureOfComposition.ProgramGraph
open FailureOfComposition.ArithmeticCodeCompiler FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.SigmaOneSearch

namespace CategoricalEssentialIncompleteness.LocalConnectedness.FiniteSwitch

attribute [local irreducible] FFL.FirstOrder.Arithmetic.code

def branchCode (c : PCode) : Code 2 :=
  codePair (Code.proj 1) (successAt c (Code.proj 0) (Code.proj 1))

def switchCode (c d : PCode) : PCode :=
  unaryCompile (codeBind (codeRfindPos (unionTest c d)) (branchCode c))

def StageAccept {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : PCode) (s x : M) : Prop :=
  Semiformula.Evalb ![s, (encode c : M), x, 0]
    (evalnCertificateFormula : ArithmeticSemisentence 4)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem branchCode_eval (c : PCode) (s x z : M) :
    Semiformula.Evalb ![z, s, x] (code (branchCode c)) ↔
      (StageAccept c s x ∧ z = pair x 1) ∨
        (¬StageAccept c s x ∧ z = pair x 0) := by
  have ht (a : M) := successAt_eval c (Code.proj (0 : Fin 2)) (Code.proj 1)
    s x a ![s, x] ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
  have hp := (eval_proj_iff (1 : Fin 2) x ![s, x]).mpr rfl
  classical
  by_cases hc : StageAccept c s x
  · have htag := (ht 1).mpr (Or.inl ⟨hc, rfl⟩)
    have hpair : Semiformula.Evalb ![pair x 1, s, x] (code (branchCode c)) :=
      eval_codePair (Code.proj 1) (successAt c (Code.proj 0) (Code.proj 1)) x 1 ![s, x] hp htag
    constructor
    · intro h; exact Or.inl ⟨hc, eval_unique h hpair⟩
    · rintro (⟨_, rfl⟩ | ⟨hn, _⟩)
      · exact hpair
      · exact False.elim (hn hc)
  · have htag := (ht 0).mpr (Or.inr ⟨hc, rfl⟩)
    have hpair : Semiformula.Evalb ![pair x 0, s, x] (code (branchCode c)) :=
      eval_codePair (Code.proj 1) (successAt c (Code.proj 0) (Code.proj 1)) x 0 ![s, x] hp htag
    constructor
    · intro h; exact Or.inr ⟨hc, eval_unique h hpair⟩
    · rintro (⟨hy, _⟩ | ⟨_, rfl⟩)
      · exact False.elim (hc hy)
      · exact hpair

theorem switchCode_eval (c d : PCode) (x z : M) :
    Computes (switchCode c d) x z ↔
      ∃ s : M, Semiformula.Evalb ![s, x] (code (codeRfindPos (unionTest c d))) ∧
        ((StageAccept c s x ∧ z = pair x 1) ∨
          (¬StageAccept c s x ∧ z = pair x 0)) := by
  rw [switchCode, computes_unaryCompile, eval_codeBind_iff]
  simp_rw [branchCode_eval]

theorem selectedStage_accepts (c d : PCode) (s x : M)
    (h : Semiformula.Evalb ![s, x] (code (codeRfindPos (unionTest c d)))) :
    StageAccept c s x ∨ StageAccept d s x :=
  (unionTest_positive c d s x).mp ((eval_codeRfindPos_iff _ s ![x]).mp h).1

theorem switchCode_domain (c d : PCode) (x : M) :
    (∃ z, Computes (switchCode c d) x z) ↔ Computes c x 0 ∨ Computes d x 0 := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨s, hs, _⟩ := (switchCode_eval c d x z).mp hz
    exact (unionSearch_domain c d x).mp ⟨s, hs⟩
  · intro h
    obtain ⟨s, hs⟩ := (unionSearch_domain c d x).mpr h
    classical
    by_cases hc : StageAccept c s x
    · exact ⟨pair x 1, (switchCode_eval c d x _).mpr ⟨s, hs, Or.inl ⟨hc, rfl⟩⟩⟩
    · exact ⟨pair x 0, (switchCode_eval c d x _).mpr ⟨s, hs, Or.inr ⟨hc, rfl⟩⟩⟩

theorem switchCode_graph (c d : PCode) (x z : M)
    (hd : ¬(Computes c x 0 ∧ Computes d x 0)) :
    Computes (switchCode c d) x z ↔
      (Computes c x 0 ∧ z = pair x 1) ∨ (Computes d x 0 ∧ z = pair x 0) := by
  have hc (s : M) (h : StageAccept c s x) : Computes c x 0 :=
    (computes_iff_stage c x 0).mpr ⟨s, h⟩
  have he (s : M) (h : StageAccept d s x) : Computes d x 0 :=
    (computes_iff_stage d x 0).mpr ⟨s, h⟩
  constructor
  · intro h
    obtain ⟨s, hs, (⟨ha, hz⟩ | ⟨ha, hz⟩)⟩ := (switchCode_eval c d x z).mp h
    · exact Or.inl ⟨hc s ha, hz⟩
    · exact Or.inr ⟨he s ((selectedStage_accepts c d s x hs).resolve_left ha), hz⟩
  · intro h
    obtain ⟨s, hs⟩ := (unionSearch_domain c d x).mpr (h.imp And.left And.left)
    rcases selectedStage_accepts c d s x hs with ha | ha
    · refine (switchCode_eval c d x z).mpr ⟨s, hs, Or.inl ⟨ha, ?_⟩⟩
      rcases h with h | h
      · exact h.2
      · exact False.elim (hd ⟨hc s ha, h.1⟩)
    · refine (switchCode_eval c d x z).mpr ⟨s, hs, Or.inr ⟨?_, ?_⟩⟩
      · exact fun hb => hd ⟨hc s hb, he s ha⟩
      · rcases h with h | h
        · exact False.elim (hd ⟨h.1, he s ha⟩)
        · exact h.2

def domainSentence (c d : PCode) : ArithmeticSentence :=
  “∀ x, (∃ z, !(eventualGraph (encode (switchCode c d))).val x z) ↔
    (!(eventualGraph (encode c)).val x 0 ∨ !(eventualGraph (encode d)).val x 0)”

def graphSentence (c d : PCode) : ArithmeticSentence :=
  “∀ x, ¬(!(eventualGraph (encode c)).val x 0 ∧ !(eventualGraph (encode d)).val x 0) →
    ∀ z, !(eventualGraph (encode (switchCode c d))).val x z ↔
      ((!(eventualGraph (encode c)).val x 0 ∧ !pairDef z x 1) ∨
        (!(eventualGraph (encode d)).val x 0 ∧ !pairDef z x 0))”

theorem pa_proves_domain (c d : PCode) : 𝗣𝗔 ⊢ domainSentence c d := by
  apply Arithmetic.complete.{0} 𝗣𝗔
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  simpa [models_iff, domainSentence, ProgramGraph.Computes] using (switchCode_domain (M := M) c d)

theorem pa_proves_graph (c d : PCode) : 𝗣𝗔 ⊢ graphSentence c d := by
  apply Arithmetic.complete.{0} 𝗣𝗔
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  have hg := fun x h z => switchCode_graph (M := M) c d x z h
  simp [ProgramGraph.Computes] at hg
  simp [models_iff, graphSentence]
  intro x hd z
  apply hg x ?_ z
  rcases hd with hd | hd
  · intro s hs
    exact False.elim (hd s hs)
  · intro _ _
    exact hd

end CategoricalEssentialIncompleteness.LocalConnectedness.FiniteSwitch
