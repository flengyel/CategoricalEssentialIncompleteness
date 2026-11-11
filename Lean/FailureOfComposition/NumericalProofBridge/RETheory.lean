/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Transfer

/-!
# Numerical proof bridges for recursively enumerable theories

This module equips every arithmetic theory with recursively enumerable axiom
codes with a fixed primitive-recursive theorem-stage test.  For theories that
extend PA in provability strength, it interprets the existing numerical proof
presentation in the theory, proves exact correspondence at the stage and graph
tags, and instantiates the accepted structural preservation theorems.

The stage test is selected separately for each fixed theory and enumerability
proof.  No effective dependence on either input is claimed.  Soundness below
means derivability in the object theory, not truth in the standard model.
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

/-! ## Theorem-stage presentations -/

/-- Recursively enumerable membership in an arithmetic theory gives
recursively enumerable codes for its axioms. -/
theorem axiomCodes_re_of_reTheory (T : ArithmeticTheory) (hT : T.RE) :
    REPred (FailureOfComposition.AxiomCodes T) := by
  have he : REPred (fun p : ℕ × ArithmeticSentence =>
      Encodable.encode p.2 = p.1) :=
    (Primrec.eq.comp (Primrec.encode.comp Primrec.snd)
      Primrec.fst).computablePred.to_re
  apply REPred.of_eq ((he.and (hT.re.comp Computable.snd)).projection)
  intro n
  simp only [FailureOfComposition.AxiomCodes,
    Sentence.quote_eq_encode_nat]

/-- A primitive-recursive Boolean stage test enumerating exactly the theorem
codes of a theory with recursively enumerable axiom codes. -/
theorem exists_reTheoryStageWitness
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    ∃ w : ℕ → ℕ → Bool,
      Primrec (fun z : ℕ × ℕ => w z.1 z.2) ∧
      ∀ a : ℕ, FailureOfComposition.TheoremCodes T a ↔
        ∃ s : ℕ, w a s = true :=
  NumericalSpecialization.exists_primrec_stage_witness
    (theorem_codes_re_of_axiom_codes T hRE)

/-- The fixed theorem-stage test selected for `T` and `hRE`. -/
noncomputable def reTheoryStageWitness
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    ℕ → ℕ → Bool :=
  Classical.choose (exists_reTheoryStageWitness T hRE)

theorem primrec_reTheoryStageWitness
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    Primrec (fun z : ℕ × ℕ =>
      reTheoryStageWitness T hRE z.1 z.2) :=
  (Classical.choose_spec (exists_reTheoryStageWitness T hRE)).1

theorem theoremCodes_iff_exists_reTheoryStage
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (a : ℕ) :
    FailureOfComposition.TheoremCodes T a ↔
      ∃ s : ℕ, reTheoryStageWitness T hRE a s = true :=
  (Classical.choose_spec (exists_reTheoryStageWitness T hRE)).2 a

theorem reTheory_provable_iff_exists_stage
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (σ : ArithmeticSentence) :
    T ⊢ σ ↔ ∃ s : ℕ,
      reTheoryStageWitness T hRE (Encodable.encode σ) s = true := by
  simpa [FailureOfComposition.TheoremCodes,
    Sentence.quote_eq_encode_nat] using
      (theoremCodes_iff_exists_reTheoryStage T hRE
        (Encodable.encode σ))

theorem reTheoryStageWitness_sound
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (a s : ℕ)
    (h : reTheoryStageWitness T hRE a s = true) :
    T ⊢ decodedSentence a := by
  have hcode : FailureOfComposition.TheoremCodes T a :=
    (theoremCodes_iff_exists_reTheoryStage T hRE a).mpr ⟨s, h⟩
  rcases hcode with ⟨σ, hσ, hprov⟩
  have hencode : Encodable.encode σ = a := by
    simpa only [Sentence.quote_eq_encode_nat] using hσ
  rw [← hencode, decodedSentence_encode]
  exact hprov

/-! ## Interpretation in an extension of PA -/

/-- Actual inclusion of the PA axioms is a direct entry point to the
provability-inclusion interface used below. -/
theorem paWeakerThanOfSubset (T : ArithmeticTheory)
    (hPA : (𝗣𝗔 : ArithmeticTheory) ⊆ T) : 𝗣𝗔 ⪯ T :=
  FFL.FirstOrder.Theory.Proof.weakerThan_of_le hPA

theorem extendedLogicalAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (extendedTheoryPresentation w).syn.logicalAxiom.Holds s) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily s :=
  WeakerThan.pbl (extendedLogicalAxiom_meaning_provable w h)

theorem extendedTheoryAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a s : ℕ, w a s = true → T ⊢ decodedSentence a)
    {u : FormulaString}
    (hu : (extendedTheoryPresentation w).ax.Holds u) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily u := by
  change axiomTest w u = true at hu
  rw [axiomTest_eq_true_iff, axiomShape_iff] at hu
  rcases hu with ⟨a, s, hw, rfl⟩ | ⟨q, rfl⟩
  · simpa using hstage a s hw
  · rw [formulaMeaning_equalityString]
    exact WeakerThan.pbl (firstSuccess_eventual_diagonal q)

theorem extendedProofLines_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a s : ℕ, w a s = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ i, i < Ψ.length →
      LineJustified (extendedTheoryPresentation w) Ψ i) :
    ∀ i, i < Ψ.length →
      T ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, hcase⟩ := hj i hi
    rcases hcase with hlog | hax | ⟨j, hji, k, hki, himp⟩
    · exact extendedLogicalAxiom_meaning_provable_in T w hlog
    · exact extendedTheoryAxiom_meaning_provable_in T w hstage hax
    · have hjlen : j < Ψ.length := Nat.lt_trans hji hi
      have hklen : k < Ψ.length := Nat.lt_trans hki hi
      have hAntecedent := ih j hji hjlen
      have hImplication := ih k hki hklen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

private theorem reTheory_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem extendedIsProofList_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a s : ℕ, w a s = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence} {u : FormulaString}
    (hΨ : IsProofList (extendedTheoryPresentation w) Ψ u) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily u := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := extendedProofLines_meaning_provable_in
    T w hstage hj (Ψ.length - 1) hidx
  rw [reTheory_getD_last_eq, hlast] at hlastLine
  exact hlastLine

/-- A numerical proof in the extended presentation denotes a sentence
derivable in `T`. -/
theorem extendedProof_T_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a s : ℕ, w a s = true → T ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extendedIsProofList_meaning_sound_in T w hstage hp

theorem extendedProof_T_equalityCode_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a s : ℕ, w a s = true → T ⊢ decodedSentence a)
    {p q r : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (equalityCode q r)) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  have h := extendedProof_T_meaning_sound_in T w hstage hp
  simpa [equalityCode, firstSuccessFamily, eventualFamily] using h

theorem extendedProof_T_leftInstanceCode_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a s : ℕ, w a s = true → T ⊢ decodedSentence a)
    {p q n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (leftInstanceCode q n m)) :
    T ⊢ (firstSuccessGraph q).val/[n, m] := by
  have h := extendedProof_T_meaning_sound_in T w hstage hp
  simpa [leftInstanceCode, firstSuccessFamily] using h

theorem extendedProof_T_rightInstanceCode_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a s : ℕ, w a s = true → T ⊢ decodedSentence a)
    {p r n m : ℕ}
    (hp : Proof_T (extendedTheoryPresentation w) p
      (rightInstanceCode r n m)) :
    T ⊢ (eventualGraph r).val/[n, m] := by
  have h := extendedProof_T_meaning_sound_in T w hstage hp
  simpa [rightInstanceCode, eventualFamily] using h

/-! ## Supplied-stage exact correspondences -/

theorem theory_provable_to_exists_stage_proof_T
    (T : ArithmeticTheory)
    (w : ℕ → ℕ → Bool)
    (henum : ∀ σ : ArithmeticSentence,
      T ⊢ σ ↔ ∃ s : ℕ, w (Encodable.encode σ) s = true)
    (σ : ArithmeticSentence)
    (hσ : T ⊢ σ) :
    ∃ s p : ℕ, Proof_T (extendedTheoryPresentation w) p
      (stageCode (Encodable.encode σ) s) := by
  obtain ⟨s, hs⟩ := (henum σ).mp hσ
  refine ⟨s, oneLineProofCode
    (stageCode (Encodable.encode σ) s), ?_⟩
  apply proof_T_old_to_extended w
  apply proof_T_oneLine_of_axiom
  rw [stageCode, decodeFormula_encodeFormula]
  exact stageAxiom_holds w (Encodable.encode σ) s hs

theorem extendedProof_T_stageCode_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    (σ : ArithmeticSentence) (s p : ℕ)
    (hp : Proof_T (extendedTheoryPresentation w) p
      (stageCode (Encodable.encode σ) s)) :
    T ⊢ σ := by
  have h := extendedProof_T_meaning_sound_in T w hstage hp
  simpa [stageCode] using h

theorem theory_provable_iff_exists_stage_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (henum : ∀ σ : ArithmeticSentence,
      T ⊢ σ ↔ ∃ s : ℕ, w (Encodable.encode σ) s = true)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    (σ : ArithmeticSentence) :
    T ⊢ σ ↔ ∃ s p : ℕ,
      Proof_T (extendedTheoryPresentation w) p
        (stageCode (Encodable.encode σ) s) := by
  constructor
  · exact theory_provable_to_exists_stage_proof_T T w henum σ
  · rintro ⟨s, p, hp⟩
    exact extendedProof_T_stageCode_sound_in T w hstage σ s p hp

theorem theory_provable_uniform_iff_exists_equalityCode_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (henum : ∀ σ : ArithmeticSentence,
      T ⊢ σ ↔ ∃ s : ℕ, w (Encodable.encode σ) s = true)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    (q r : ℕ) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) ↔
      ∃ p : ℕ, Proof_T (extendedTheoryPresentation w) p
        (equalityCode q r) := by
  constructor
  · intro h
    obtain ⟨s, p, hp⟩ :=
      (theory_provable_iff_exists_stage_proof_T T w henum hstage
        (uniformSentence (firstSuccessGraph q) (eventualGraph r))).mp h
    refine ⟨bridgeEquality p s q r, ?_⟩
    apply proof_T_bridgeEquality w
    simpa [eqSentenceCode] using hp
  · rintro ⟨p, hp⟩
    exact extendedProof_T_equalityCode_sound_in T w hstage hp

private noncomputable def theoryLeftBridgeSentence (q n m : ℕ) :
    ArithmeticSentence :=
  (firstSuccessGraph q).val/[n, m]

private noncomputable def theoryRightBridgeSentence (r n m : ℕ) :
    ArithmeticSentence :=
  (eventualGraph r).val/[n, m]

private theorem theoryLeftBridgeSentence_eq (q n m : ℕ) :
    theoryLeftBridgeSentence q n m =
      (firstSuccessGraph q).val/[n, m] :=
  rfl

private theorem theoryRightBridgeSentence_eq (r n m : ℕ) :
    theoryRightBridgeSentence r n m =
      (eventualGraph r).val/[n, m] :=
  rfl

private theorem encode_theoryLeftBridgeSentence (q n m : ℕ) :
    Encodable.encode (theoryLeftBridgeSentence q n m) =
      leftSentenceCode q n m := by
  rw [theoryLeftBridgeSentence_eq]
  rfl

private theorem encode_theoryRightBridgeSentence (r n m : ℕ) :
    Encodable.encode (theoryRightBridgeSentence r n m) =
      rightSentenceCode r n m := by
  rw [theoryRightBridgeSentence_eq]
  rfl

theorem theory_provable_left_iff_exists_leftInstanceCode_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (henum : ∀ σ : ArithmeticSentence,
      T ⊢ σ ↔ ∃ s : ℕ, w (Encodable.encode σ) s = true)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    (q n m : ℕ) :
    T ⊢ (firstSuccessGraph q).val/[n, m] ↔
      ∃ p : ℕ, Proof_T (extendedTheoryPresentation w) p
        (leftInstanceCode q n m) := by
  constructor
  · intro h
    have hsentence : T ⊢ theoryLeftBridgeSentence q n m := by
      rw [theoryLeftBridgeSentence_eq]
      exact h
    obtain ⟨s, p, hp⟩ :=
      (theory_provable_iff_exists_stage_proof_T T w henum hstage
        (theoryLeftBridgeSentence q n m)).mp hsentence
    rw [encode_theoryLeftBridgeSentence] at hp
    refine ⟨bridgeLeft p s q n m, ?_⟩
    apply proof_T_bridgeLeft w
    exact hp
  · rintro ⟨p, hp⟩
    exact extendedProof_T_leftInstanceCode_sound_in T w hstage hp

theorem theory_provable_right_iff_exists_rightInstanceCode_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (henum : ∀ σ : ArithmeticSentence,
      T ⊢ σ ↔ ∃ s : ℕ, w (Encodable.encode σ) s = true)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    (r n m : ℕ) :
    T ⊢ (eventualGraph r).val/[n, m] ↔
      ∃ p : ℕ, Proof_T (extendedTheoryPresentation w) p
        (rightInstanceCode r n m) := by
  constructor
  · intro h
    have hsentence : T ⊢ theoryRightBridgeSentence r n m := by
      rw [theoryRightBridgeSentence_eq]
      exact h
    obtain ⟨s, p, hp⟩ :=
      (theory_provable_iff_exists_stage_proof_T T w henum hstage
        (theoryRightBridgeSentence r n m)).mp hsentence
    rw [encode_theoryRightBridgeSentence] at hp
    refine ⟨bridgeRight p s r n m, ?_⟩
    apply proof_T_bridgeRight w
    exact hp
  · rintro ⟨p, hp⟩
    exact extendedProof_T_rightInstanceCode_sound_in T w hstage hp

/-! ## The selected presentation for an r.e. theory -/

noncomputable def reTheoryExtendedTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    TheoryPresentation :=
  extendedTheoryPresentation (reTheoryStageWitness T hRE)

noncomputable def reTheoryExtendedPRTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    PRTheoryPresentation :=
  extendedPRTheoryPresentation (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

noncomputable def reTheoryExtendedProofGraph
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 2 :=
  extendedProofGraph (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem reTheoryExtendedProofGraph_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (reTheoryExtendedProofGraph T hRE).val ↔
      Proof_T (reTheoryExtendedTheoryPresentation T hRE) p a := by
  exact extendedProofGraph_nat_iff
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE) p a

theorem reTheoryExtendedProof_T_meaning_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p a : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) := by
  exact extendedProof_T_meaning_sound_in T
    (reTheoryStageWitness T hRE)
    (reTheoryStageWitness_sound T hRE) hp

theorem reTheory_provable_iff_exists_stage_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (σ : ArithmeticSentence) :
    T ⊢ σ ↔ ∃ s p : ℕ,
      Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
        (stageCode (Encodable.encode σ) s) := by
  exact theory_provable_iff_exists_stage_proof_T T
    (reTheoryStageWitness T hRE)
    (reTheory_provable_iff_exists_stage T hRE)
    (reTheoryStageWitness_sound T hRE) σ

theorem reTheory_provable_uniform_iff_exists_equalityCode_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (q r : ℕ) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) ↔
      ∃ p : ℕ, Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
        (equalityCode q r) := by
  exact theory_provable_uniform_iff_exists_equalityCode_proof_T T
    (reTheoryStageWitness T hRE)
    (reTheory_provable_iff_exists_stage T hRE)
    (reTheoryStageWitness_sound T hRE) q r

theorem reTheory_provable_left_iff_exists_leftInstanceCode_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (q n m : ℕ) :
    T ⊢ (firstSuccessGraph q).val/[n, m] ↔
      ∃ p : ℕ, Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
        (leftInstanceCode q n m) := by
  exact theory_provable_left_iff_exists_leftInstanceCode_proof_T T
    (reTheoryStageWitness T hRE)
    (reTheory_provable_iff_exists_stage T hRE)
    (reTheoryStageWitness_sound T hRE) q n m

theorem reTheory_provable_right_iff_exists_rightInstanceCode_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (r n m : ℕ) :
    T ⊢ (eventualGraph r).val/[n, m] ↔
      ∃ p : ℕ, Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
        (rightInstanceCode r n m) := by
  exact theory_provable_right_iff_exists_rightInstanceCode_proof_T T
    (reTheoryStageWitness T hRE)
    (reTheory_provable_iff_exists_stage T hRE)
    (reTheoryStageWitness_sound T hRE) r n m

/-! ## Bridge and transfer instances -/

theorem reTheoryProof_T_bridgeEquality
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p s q r : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (stageCode (eqSentenceCode q r) s)) :
    Proof_T (reTheoryExtendedTheoryPresentation T hRE)
      (bridgeEquality p s q r) (equalityCode q r) :=
  proof_T_bridgeEquality (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_bridgeLeft
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p s q n m : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (stageCode (leftSentenceCode q n m) s)) :
    Proof_T (reTheoryExtendedTheoryPresentation T hRE)
      (bridgeLeft p s q n m) (leftInstanceCode q n m) :=
  proof_T_bridgeLeft (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_bridgeRight
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p s r n m : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (stageCode (rightSentenceCode r n m) s)) :
    Proof_T (reTheoryExtendedTheoryPresentation T hRE)
      (bridgeRight p s r n m) (rightInstanceCode r n m) :=
  proof_T_bridgeRight (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_transferForwardFromStages
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p h sEq sLeft q r n m : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T (reTheoryExtendedTheoryPresentation T hRE) h
      (stageCode (leftSentenceCode q n m) sLeft)) :
    Proof_T (reTheoryExtendedTheoryPresentation T hRE)
      (transferForwardFromStages p h sEq sLeft q r n m)
      (rightInstanceCode r n m) :=
  proof_T_transferForwardFromStages (reTheoryStageWitness T hRE) hp hh

theorem reTheoryProof_T_transferReverseFromStages
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p h sEq sRight q r n m : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T (reTheoryExtendedTheoryPresentation T hRE) h
      (stageCode (rightSentenceCode r n m) sRight)) :
    Proof_T (reTheoryExtendedTheoryPresentation T hRE)
      (transferReverseFromStages p h sEq sRight q r n m)
      (leftInstanceCode q n m) :=
  proof_T_transferReverseFromStages (reTheoryStageWitness T hRE) hp hh

theorem reTheory_transferForwardFromStages_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p h sEq sLeft q r n m : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T (reTheoryExtendedTheoryPresentation T hRE) h
      (stageCode (leftSentenceCode q n m) sLeft)) :
    T ⊢ (eventualGraph r).val/[n, m] := by
  apply extendedProof_T_rightInstanceCode_sound_in T
    (reTheoryStageWitness T hRE)
    (reTheoryStageWitness_sound T hRE)
  exact reTheoryProof_T_transferForwardFromStages T hRE hp hh

theorem reTheory_transferReverseFromStages_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p h sEq sRight q r n m : ℕ}
    (hp : Proof_T (reTheoryExtendedTheoryPresentation T hRE) p
      (stageCode (eqSentenceCode q r) sEq))
    (hh : Proof_T (reTheoryExtendedTheoryPresentation T hRE) h
      (stageCode (rightSentenceCode r n m) sRight)) :
    T ⊢ (firstSuccessGraph q).val/[n, m] := by
  apply extendedProof_T_leftInstanceCode_sound_in T
    (reTheoryStageWitness T hRE)
    (reTheoryStageWitness_sound T hRE)
  exact reTheoryProof_T_transferReverseFromStages T hRE hp hh

/-! ## Structural preservation for the selected stage test -/

theorem provable_PA_reTheoryEqualityBridgePreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformEqualityBridgePreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformEqualityBridgePreservation
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryLeftBridgePreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformLeftBridgePreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformLeftBridgePreservation
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryRightBridgePreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformRightBridgePreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformRightBridgePreservation
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryForwardFromStagesPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformForwardFromStagesPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformForwardFromStagesPreservation
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryReverseFromStagesPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformReverseFromStagesPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformReverseFromStagesPreservation
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem provable_T_reTheoryEqualityBridgePreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformEqualityBridgePreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryEqualityBridgePreservation T hRE)

theorem provable_T_reTheoryLeftBridgePreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformLeftBridgePreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryLeftBridgePreservation T hRE)

theorem provable_T_reTheoryRightBridgePreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformRightBridgePreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryRightBridgePreservation T hRE)

theorem provable_T_reTheoryForwardFromStagesPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformForwardFromStagesPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryForwardFromStagesPreservation T hRE)

theorem provable_T_reTheoryReverseFromStagesPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformReverseFromStagesPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryReverseFromStagesPreservation T hRE)

/-! ## Boundary applications -/

/-- The general supplied-stage theorem specializes to the accepted PA stage
witness without identifying it with any witness chosen by `hRE`. -/
theorem PA_provable_iff_exists_stage_proof_T_from_general_api
    (σ : ArithmeticSentence) :
    𝗣𝗔 ⊢ σ ↔ ∃ s p : ℕ,
      Proof_T paExtendedTheoryPresentation p
        (stageCode (Encodable.encode σ) s) := by
  exact theory_provable_iff_exists_stage_proof_T 𝗣𝗔 paStageWitness
    PA_provable_iff_exists_stage NumericalSpecialization.paStageWitness_sound σ

/-- PA with one additional arithmetic sentence as an axiom. -/
def paSingletonExtension (σ : ArithmeticSentence) : ArithmeticTheory :=
  𝗣𝗔 ∪ {σ}

theorem paSingletonExtension_re (σ : ArithmeticSentence) :
    (paSingletonExtension σ).RE := by
  apply FFL.FirstOrder.Theory.RE.add
  · infer_instance
  · exact FFL.FirstOrder.Theory.RE.ofFinite (Set.finite_singleton σ)

theorem paSingletonExtension_axiomCodes_re (σ : ArithmeticSentence) :
    REPred (FailureOfComposition.AxiomCodes
      (paSingletonExtension σ)) :=
  axiomCodes_re_of_reTheory (paSingletonExtension σ)
    (paSingletonExtension_re σ)

theorem paSingletonExtension_axiom_to_stage_proof
    (σ : ArithmeticSentence)
    (hσ : σ ∈ paSingletonExtension σ) :
    ∃ s p : ℕ,
      Proof_T
        (reTheoryExtendedTheoryPresentation
          (paSingletonExtension σ)
          (paSingletonExtension_axiomCodes_re σ)) p
        (stageCode (Encodable.encode σ) s) := by
  let _ : 𝗣𝗔 ⪯ paSingletonExtension σ :=
    paWeakerThanOfSubset (paSingletonExtension σ) (by
      simp [paSingletonExtension])
  apply (reTheory_provable_iff_exists_stage_proof_T
    (paSingletonExtension σ)
    (paSingletonExtension_axiomCodes_re σ) σ).mp
  exact Entailment.by_axm hσ

theorem paSingletonExtension_added_axiom_has_stage_proof
    (σ : ArithmeticSentence) :
    ∃ s p : ℕ,
      Proof_T
        (reTheoryExtendedTheoryPresentation
          (paSingletonExtension σ)
          (paSingletonExtension_axiomCodes_re σ)) p
        (stageCode (Encodable.encode σ) s) := by
  apply paSingletonExtension_axiom_to_stage_proof σ
  simp [paSingletonExtension]

end FailureOfComposition.NumericalProofBridge
