/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Presentation
public import FailureOfComposition.NumericalSpecialization

/-!
# Soundness and exact correspondence for proof-presentation bridges

This layer proves arithmetic soundness of the extended presentation and
identifies PA provability with proofs at the numerical graph tags.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open Arith.FixedFormulaNumeralSubstitution
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator
open FFL.FirstOrder.Arithmetic.Bootstrapping

/-! ## Arithmetic soundness of the extended presentation -/

theorem provable_PA_meaning_bridgeEquality (q r s : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (bridgeEqualityAxiomString q r s) := by
  simp only [bridgeEqualityAxiomString, formulaMeaning_impString,
    formulaMeaning_stageString, formulaMeaning_equalityString,
    eqSentenceCode, decodedSentence_encode, firstSuccessFamily,
    eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro V _ _
  simp [models_iff]

theorem provable_PA_meaning_bridgeLeft (q n m s : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (bridgeLeftAxiomString q n m s) := by
  simp only [bridgeLeftAxiomString, formulaMeaning_impString,
    formulaMeaning_stageString, formulaMeaning_leftInstanceString,
    leftSentenceCode, decodedSentence_encode, firstSuccessFamily]
  apply complete.{0} 𝗣𝗔
  intro V _ _
  simp [models_iff]

theorem provable_PA_meaning_bridgeRight (r n m s : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (bridgeRightAxiomString r n m s) := by
  simp only [bridgeRightAxiomString, formulaMeaning_impString,
    formulaMeaning_stageString, formulaMeaning_rightInstanceString,
    rightSentenceCode, decodedSentence_encode, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro V _ _
  simp [models_iff]

theorem extendedLogicalAxiom_meaning_provable
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (extendedTheoryPresentation w).syn.logicalAxiom.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  change extendedLogicalAxiomTest s = true at h
  rw [extendedLogicalAxiomTest_eq_true_iff] at h
  rcases h with hold | hbridge
  · apply logicalAxiom_meaning_provable
      firstSuccessFamily eventualFamily w
    exact (logicalAxiomTest_eq_true_iff s).mpr hold
  · rw [bridgeAxiomShape_iff] at hbridge
    rcases hbridge with ⟨q, r, k, rfl⟩ | ⟨q, n, m, k, rfl⟩ |
        ⟨r, n, m, k, rfl⟩
    · exact provable_PA_meaning_bridgeEquality q r k
    · exact provable_PA_meaning_bridgeLeft q n m k
    · exact provable_PA_meaning_bridgeRight r n m k

theorem extendedTheoryAxiom_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {s : FormulaString}
    (h : (extendedTheoryPresentation w).ax.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  apply theoryAxiom_meaning_provable
    firstSuccessFamily eventualFamily w hstage firstSuccess_eventual_diagonal
  simpa [extendedTheoryPresentation, specializationTheoryPresentation] using h

private theorem bridge_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem extendedProofLines_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ i, i < Ψ.length →
      LineJustified (extendedTheoryPresentation w) Ψ i) :
    ∀ i, i < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, hcase⟩ := hj i hi
    rcases hcase with hlog | hax | ⟨j, hji, k, hki, himp⟩
    · exact extendedLogicalAxiom_meaning_provable w hlog
    · exact extendedTheoryAxiom_meaning_provable w hstage hax
    · have hjlen : j < Ψ.length := Nat.lt_trans hji hi
      have hklen : k < Ψ.length := Nat.lt_trans hki hi
      have hAntecedent := ih j hji hjlen
      have hImplication := ih k hki hklen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem extendedIsProofList_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence} {s : FormulaString}
    (hΨ : IsProofList (extendedTheoryPresentation w) Ψ s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := extendedProofLines_meaning_provable w hstage hj
    (Ψ.length - 1) hidx
  rw [bridge_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem extendedProof_T_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extendedIsProofList_meaning_sound w hstage hp

private theorem paBridgeStageWitness_sound (a k : ℕ)
    (h : paStageWitness a k = true) :
    𝗣𝗔 ⊢ decodedSentence a := by
  exact NumericalSpecialization.paStageWitness_sound a k h

noncomputable def paExtendedTheoryPresentation : TheoryPresentation :=
  extendedTheoryPresentation paStageWitness

noncomputable def paExtendedPRTheoryPresentation : PRTheoryPresentation :=
  extendedPRTheoryPresentation paStageWitness primrec_paStageWitness

theorem paExtendedProof_T_meaning_sound {p a : ℕ}
    (hp : Proof_T paExtendedTheoryPresentation p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) := by
  exact extendedProof_T_meaning_sound paStageWitness
    paBridgeStageWitness_sound hp

theorem paProof_T_old_to_extended {p a : ℕ}
    (hp : Proof_T paSpecializationTheoryPresentation p a) :
    Proof_T paExtendedTheoryPresentation p a :=
  proof_T_old_to_extended paStageWitness hp

theorem paExtendedProof_T_equalityCode_sound {p q r : ℕ}
    (hp : Proof_T paExtendedTheoryPresentation p (equalityCode q r)) :
    𝗣𝗔 ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  have h := paExtendedProof_T_meaning_sound hp
  simpa [equalityCode, firstSuccessFamily, eventualFamily] using h

theorem paExtendedProof_T_leftInstanceCode_sound {p q n m : ℕ}
    (hp : Proof_T paExtendedTheoryPresentation p
      (leftInstanceCode q n m)) :
    𝗣𝗔 ⊢ (firstSuccessGraph q).val/[n, m] := by
  have h := paExtendedProof_T_meaning_sound hp
  simpa [leftInstanceCode, firstSuccessFamily] using h

theorem paExtendedProof_T_rightInstanceCode_sound {p r n m : ℕ}
    (hp : Proof_T paExtendedTheoryPresentation p
      (rightInstanceCode r n m)) :
    𝗣𝗔 ⊢ (eventualGraph r).val/[n, m] := by
  have h := paExtendedProof_T_meaning_sound hp
  simpa [rightInstanceCode, eventualFamily] using h

/-! ## Exact correspondence at the graph tags -/

private noncomputable def leftBridgeSentence (q n m : ℕ) :
    ArithmeticSentence :=
  (firstSuccessGraph q).val/[n, m]

private noncomputable def rightBridgeSentence (r n m : ℕ) :
    ArithmeticSentence :=
  (eventualGraph r).val/[n, m]

private theorem leftBridgeSentence_eq (q n m : ℕ) :
    leftBridgeSentence q n m = (firstSuccessGraph q).val/[n, m] :=
  rfl

private theorem rightBridgeSentence_eq (r n m : ℕ) :
    rightBridgeSentence r n m = (eventualGraph r).val/[n, m] :=
  rfl

private theorem encode_leftBridgeSentence (q n m : ℕ) :
    Encodable.encode (leftBridgeSentence q n m) =
      leftSentenceCode q n m := by
  rw [leftBridgeSentence_eq]
  rfl

private theorem encode_rightBridgeSentence (r n m : ℕ) :
    Encodable.encode (rightBridgeSentence r n m) =
      rightSentenceCode r n m := by
  rw [rightBridgeSentence_eq]
  rfl

theorem PA_provable_uniform_iff_exists_equalityCode_proof_T (q r : ℕ) :
    𝗣𝗔 ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) ↔
      ∃ p : ℕ, Proof_T paExtendedTheoryPresentation p
        (equalityCode q r) := by
  constructor
  · intro h
    obtain ⟨s, p, hp⟩ :=
      (PA_provable_iff_exists_stage_proof_T
        (uniformSentence (firstSuccessGraph q) (eventualGraph r))).mp h
    refine ⟨bridgeEquality p s q r, ?_⟩
    apply proof_T_bridgeEquality paStageWitness
    apply paProof_T_old_to_extended
    simpa [eqSentenceCode] using hp
  · rintro ⟨p, hp⟩
    exact paExtendedProof_T_equalityCode_sound hp

theorem PA_provable_left_iff_exists_leftInstanceCode_proof_T
    (q n m : ℕ) :
    𝗣𝗔 ⊢ (firstSuccessGraph q).val/[n, m] ↔
      ∃ p : ℕ, Proof_T paExtendedTheoryPresentation p
        (leftInstanceCode q n m) := by
  constructor
  · intro h
    have hsentence : 𝗣𝗔 ⊢ leftBridgeSentence q n m := by
      rw [leftBridgeSentence_eq]
      exact h
    obtain ⟨s, p, hp⟩ :=
      (PA_provable_iff_exists_stage_proof_T
        (leftBridgeSentence q n m)).mp hsentence
    rw [encode_leftBridgeSentence] at hp
    refine ⟨bridgeLeft p s q n m, ?_⟩
    apply proof_T_bridgeLeft paStageWitness
    apply paProof_T_old_to_extended
    exact hp
  · rintro ⟨p, hp⟩
    exact paExtendedProof_T_leftInstanceCode_sound hp

theorem PA_provable_right_iff_exists_rightInstanceCode_proof_T
    (r n m : ℕ) :
    𝗣𝗔 ⊢ (eventualGraph r).val/[n, m] ↔
      ∃ p : ℕ, Proof_T paExtendedTheoryPresentation p
        (rightInstanceCode r n m) := by
  constructor
  · intro h
    have hsentence : 𝗣𝗔 ⊢ rightBridgeSentence r n m := by
      rw [rightBridgeSentence_eq]
      exact h
    obtain ⟨s, p, hp⟩ :=
      (PA_provable_iff_exists_stage_proof_T
        (rightBridgeSentence r n m)).mp hsentence
    rw [encode_rightBridgeSentence] at hp
    refine ⟨bridgeRight p s r n m, ?_⟩
    apply proof_T_bridgeRight paStageWitness
    apply paProof_T_old_to_extended
    exact hp
  · rintro ⟨p, hp⟩
    exact paExtendedProof_T_rightInstanceCode_sound hp

end FailureOfComposition.NumericalProofBridge
