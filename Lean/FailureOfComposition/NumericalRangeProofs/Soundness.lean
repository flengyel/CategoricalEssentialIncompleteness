/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalRangeProofs.Core
public import FailureOfComposition.PiOneExtensionality

/-!
# Soundness of the numerical range-proof presentation

The computation scheme is sound because its recognizer verifies the supplied
finite evaluator stage.  The range-introduction scheme is sound for fixed
external indices `e` and `r` once a fixed PA derivation identifies the graph
of `r` with the range partial identity of `e`.  No effective selection of `r`
from `e` is used.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalRangeProofs

open ConcreteEvaluator ConcreteIndices NumericalProofBridge
open NumericalSpecialization PiOneCharacterization ProofSearch

/-! ## Arithmetic meaning of the two new schemes -/

/-- A verified standard evaluator stage supplies a PA proof of the
stage-tagged closed graph instance. -/
theorem provable_PA_meaning_computation
    (q s u i : ℕ) (hs : stageComputation s q u i) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (computationAxiomString q s u i) := by
  have hgraph : (eventualGraph q).val.Evalb ![u, i] := by
    rw [eventualGraph_eval]
    exact ⟨s, by simpa [stageComputation] using hs⟩
  have hp := true_graph_instance_provable (eventualGraph q) u i hgraph
  simpa [computationAxiomString, rightSentenceCode, graphInstance,
    eventualFamily] using hp

/-- For fixed external indices, a PA-uniform realization of the range graph
proves every standard instance of range introduction.  The input and output
inside each displayed graph instance are standard numerals; the witness used
in an arbitrary PA model is their internal numeral. -/
theorem provable_PA_meaning_rangeIntro
    {e r : ℕ}
    (hr : Uniform 𝗣𝗔 (eventualGraph r) (rangeGraph e))
    (u i : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (rangeIntroAxiomString e r u i) := by
  simp only [rangeIntroAxiomString, formulaMeaning_impString,
    formulaMeaning_rightInstanceString, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have heq := consequence_iff.mp (Theory.Proof.sound hr) M inferInstance
  simp only [models_iff, uniformSentence_eval] at heq
  have hsemantic :
      (eventualGraph e).val.Evalb
          ![(ORingStructure.numeral u : M),
            (ORingStructure.numeral i : M)] →
      (eventualGraph r).val.Evalb
          ![(ORingStructure.numeral i : M),
            (ORingStructure.numeral i : M)] := by
    intro hei
    apply (heq _ _).mpr
    rw [rangeGraph_eval]
    exact ⟨rfl, ORingStructure.numeral u, hei⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

/-! ## Soundness of every checker proof -/

theorem rangeLogicalAxiom_meaning_provable
    (e r : ℕ)
    (hr : Uniform 𝗣𝗔 (eventualGraph r) (rangeGraph e))
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (rangeTheoryPresentation e r w).syn.logicalAxiom.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  change rangeLogicalAxiomTest e r x = true at h
  rw [rangeLogicalAxiomTest_eq_true_iff] at h
  rcases h with hold | hcomp | hrange
  · apply extendedLogicalAxiom_meaning_provable w
    exact (extendedLogicalAxiomTest_eq_true_iff x).mpr hold
  · rw [computationAxiomShape_iff] at hcomp
    obtain ⟨q, s, u, i, hs, rfl⟩ := hcomp
    exact provable_PA_meaning_computation q s u i hs
  · rw [rangeIntroAxiomShape_iff] at hrange
    obtain ⟨u, i, rfl⟩ := hrange
    exact provable_PA_meaning_rangeIntro hr u i

theorem rangeTheoryAxiom_meaning_provable
    (e r : ℕ) (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (rangeTheoryPresentation e r w).ax.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply extendedTheoryAxiom_meaning_provable w hstage
  simpa [extendedTheoryPresentation, rangeTheoryPresentation] using h

private theorem range_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem rangeProofLines_meaning_provable
    (e r : ℕ)
    (hr : Uniform 𝗣𝗔 (eventualGraph r) (rangeGraph e))
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ j, j < Ψ.length →
      LineJustified (rangeTheoryPresentation e r w) Ψ j) :
    ∀ j, j < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨a, haj, b, hbj, himp⟩
    · exact rangeLogicalAxiom_meaning_provable e r hr w hlog
    · exact rangeTheoryAxiom_meaning_provable e r w hstage hax
    · have halen : a < Ψ.length := Nat.lt_trans haj hjlt
      have hblen : b < Ψ.length := Nat.lt_trans hbj hjlt
      have hAntecedent := ih a haj halen
      have hImplication := ih b hbj hblen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem rangeIsProofList_meaning_sound
    (e r : ℕ)
    (hr : Uniform 𝗣𝗔 (eventualGraph r) (rangeGraph e))
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence} {x : FormulaString}
    (hΨ : IsProofList (rangeTheoryPresentation e r w) Ψ x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := rangeProofLines_meaning_provable e r hr w hstage hj
    (Ψ.length - 1) hidx
  rw [range_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem rangeProof_T_meaning_sound
    (e r : ℕ)
    (hr : Uniform 𝗣𝗔 (eventualGraph r) (rangeGraph e))
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (rangeTheoryPresentation e r w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  rangeIsProofList_meaning_sound e r hr w hstage hp

theorem paRangeProof_T_rightInstanceCode_sound
    {e r p n m : ℕ}
    (hr : Uniform 𝗣𝗔 (eventualGraph r) (rangeGraph e))
    (hp : Proof_T (paRangeTheoryPresentation e r) p
      (rightInstanceCode r n m)) :
    𝗣𝗔 ⊢ (eventualGraph r).val/[n, m] := by
  have h := rangeProof_T_meaning_sound e r hr paStageWitness
    paStageWitness_sound hp
  simpa [paRangeTheoryPresentation, rightInstanceCode, eventualFamily] using h

/-! ## Correctness of the total numerical map -/

theorem paRangeProof_correct
    {e r s u i : ℕ}
    (hs : stageComputation s e u i) :
    Proof_T (paRangeTheoryPresentation e r)
      (rangeProof e r s u i) (rightInstanceCode r i i) :=
  proof_T_rangeProof e r paStageWitness hs

/-- A valid supplied computation code therefore gives the exact PA
range-fixpoint endpoint, independently of any semantic soundness assumption. -/
theorem PA_proves_rangeFixpoint_of_stageComputation
    {e r s u i : ℕ}
    (hr : Uniform 𝗣𝗔 (eventualGraph r) (rangeGraph e))
    (hs : stageComputation s e u i) :
    𝗣𝗔 ⊢ (eventualGraph r).val/[i, i] :=
  paRangeProof_T_rightInstanceCode_sound hr (paRangeProof_correct hs)

end FailureOfComposition.NumericalRangeProofs
