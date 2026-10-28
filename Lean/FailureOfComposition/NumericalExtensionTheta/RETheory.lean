/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionTheta.Structural.Preservation
import FailureOfComposition.NumericalExtensionComposition.RETheory

/-!
# B1(8) proof maps for recursively enumerable theories

For an arithmetic theory extending PA with recursively enumerable axiom
codes, this module selects `reTheoryStageWitness T hRE` in the common theta
presentation.  It gives exact proof-existence correspondences for the
consumed `R`, `C`, and `X` tags and the produced `H` tag, followed by the two
supplied-code maps and the PA and `T` preservation theorems.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionTheta

open ConcreteEvaluator FiniteExtensionChecker NumericalExtensionComposition
open NumericalExtensionProofs NumericalProofBridge ProofSearch

noncomputable section

/-! ## Soundness in an extension of PA -/

theorem extensionThetaLogicalAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (extensionThetaTheoryPresentation w).syn.logicalAxiom.Holds x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x :=
  WeakerThan.pbl (extensionThetaLogicalAxiom_meaning_provable w h)

theorem extensionThetaTheoryAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (extensionThetaTheoryPresentation w).ax.Holds x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply extensionCompositionTheoryAxiom_meaning_provable_in T w hstage
  simpa [extensionCompositionTheoryPresentation,
    extensionThetaTheoryPresentation] using h

theorem extensionThetaProofLines_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ps : ProofSequence}
    (hj : ∀ j, j < Ps.length →
      LineJustified (extensionThetaTheoryPresentation w) Ps j) :
    ∀ j, j < Ps.length →
      T ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ps.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact extensionThetaLogicalAxiom_meaning_provable_in T w hlog
    · exact extensionThetaTheoryAxiom_meaning_provable_in
        T w hstage hax
    · have hulen : u < Ps.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ps.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

private theorem extensionTheta_reTheory_getD_last_eq
    (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem extensionThetaIsProofList_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ps : ProofSequence} {x : FormulaString}
    (hPs : IsProofList (extensionThetaTheoryPresentation w) Ps x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hPs
  have hidx : Ps.length - 1 < Ps.length := by
    have : 0 < Ps.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := extensionThetaProofLines_meaning_provable_in
    T w hstage hj (Ps.length - 1) hidx
  rw [extensionTheta_reTheory_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem extensionThetaProof_T_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (extensionThetaTheoryPresentation w) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extensionThetaIsProofList_meaning_sound_in T w hstage hp

/-! ## The selected common presentation -/

def reTheoryExtensionThetaTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    TheoryPresentation :=
  extensionThetaTheoryPresentation (reTheoryStageWitness T hRE)

def reTheoryExtensionThetaPRTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    PRTheoryPresentation :=
  extensionThetaPRTheoryPresentation (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

def reTheoryExtensionThetaProofGraph
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 2 :=
  extensionThetaProofGraph (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem reTheoryExtensionThetaProofGraph_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (reTheoryExtensionThetaProofGraph T hRE).val ↔
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p a :=
  extensionThetaProofGraph_nat_iff
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE) p a

theorem reTheoryExtensionThetaProof_T_meaning_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p a : ℕ}
    (hp : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extensionThetaProof_T_meaning_sound_in T
    (reTheoryStageWitness T hRE) (reTheoryStageWitness_sound T hRE) hp

theorem reTheoryExtensionThetaProof_T_rightInstanceCode_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p r n m : ℕ}
    (hp : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p
      (rightInstanceCode r n m)) :
    T ⊢ (eventualGraph r).val/[n, m] := by
  have h := reTheoryExtensionThetaProof_T_meaning_sound T hRE hp
  simpa [rightInstanceCode, eventualFamily] using h

/-! ## Exact endpoint correspondences -/

theorem reTheory_provable_right_iff_exists_extensionThetaProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (r n m : ℕ) :
    T ⊢ (eventualGraph r).val/[n, m] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (rightInstanceCode r n m) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (reTheory_provable_right_iff_exists_extensionCompositionProof_T
        T hRE r n m).mp h
    exact ⟨p, proof_T_extensionComposition_to_extensionTheta
      (reTheoryStageWitness T hRE) hp⟩
  · rintro ⟨p, hp⟩
    exact reTheoryExtensionThetaProof_T_rightInstanceCode_sound
      T hRE hp

theorem reTheory_provable_checker_iff_exists_extensionThetaProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ (eventualGraph extensionCheckerIndex).val/[Nat.pair c i,
        Nat.pair c i] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (checkerInstanceCode c i) := by
  simpa using
    reTheory_provable_right_iff_exists_extensionThetaProof_T
      T hRE extensionCheckerIndex (Nat.pair c i) (Nat.pair c i)

theorem reTheory_provable_zeroTest_iff_exists_extensionThetaProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ (eventualGraph zeroTestIndex).val/[Nat.pair c i, (0 : ℕ)] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (extensionInstanceCode c i) := by
  simpa using
    reTheory_provable_right_iff_exists_extensionThetaProof_T
      T hRE zeroTestIndex (Nat.pair c i) 0

theorem reTheory_provable_extension_iff_exists_thetaCheckerProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ extensionFormula.val/[c, i] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (checkerInstanceCode c i) :=
  (proves_checker_iff_extension T c i).symm.trans
    (reTheory_provable_checker_iff_exists_extensionThetaProof_T
      T hRE c i)

theorem reTheory_provable_extension_iff_exists_thetaExtensionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ extensionFormula.val/[c, i] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (extensionInstanceCode c i) :=
  (proves_zeroTest_iff_extension T c i).symm.trans
    (reTheory_provable_zeroTest_iff_exists_extensionThetaProof_T
      T hRE c i)

theorem reTheory_provable_theta_iff_exists_extensionThetaProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (q t i : ℕ) :
    T ⊢ (eventualGraph (thetaIndex q)).val/[Nat.pair t i, i] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (thetaInstanceCode q t i) := by
  simpa [thetaInstanceCode_eq_right] using
    reTheory_provable_right_iff_exists_extensionThetaProof_T
      T hRE (thetaIndex q) (Nat.pair t i) i

/-! ## Supplied-code maps -/

theorem reTheoryProof_T_componentAndCheckerToTheta
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p s q t c i : ℕ}
    (hp : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p
      (rightInstanceCode q t c))
    (hs : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) s
      (checkerInstanceCode c i)) :
    Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE)
      (componentAndCheckerToTheta p s q t c i)
      (thetaInstanceCode q t i) :=
  proof_T_componentAndCheckerToTheta
    (reTheoryStageWitness T hRE) hp hs

theorem reTheoryProof_T_componentAndExtToTheta
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p s q t c i : ℕ}
    (hp : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p
      (rightInstanceCode q t c))
    (hs : Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) s
      (extensionInstanceCode c i)) :
    Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE)
      (componentAndExtToTheta p s q t c i)
      (thetaInstanceCode q t i) :=
  proof_T_componentAndExtToTheta
    (reTheoryStageWitness T hRE) hp hs

/-- The supplied-code B1(8) transformation stated explicitly for PA. -/
theorem reTheoryPAProof_T_componentAndCheckerToTheta
    (hRE : REPred (FailureOfComposition.AxiomCodes 𝗣𝗔))
    {p s q t c i : ℕ}
    (hp : Proof_T (reTheoryExtensionThetaTheoryPresentation 𝗣𝗔 hRE) p
      (rightInstanceCode q t c))
    (hs : Proof_T (reTheoryExtensionThetaTheoryPresentation 𝗣𝗔 hRE) s
      (checkerInstanceCode c i)) :
    Proof_T (reTheoryExtensionThetaTheoryPresentation 𝗣𝗔 hRE)
      (componentAndCheckerToTheta p s q t c i)
      (thetaInstanceCode q t i) :=
  reTheoryProof_T_componentAndCheckerToTheta 𝗣𝗔 hRE hp hs

/-! ## Internal preservation in PA and in `T` -/

theorem provable_PA_reTheoryComponentAndCheckerToThetaPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformComponentAndCheckerToThetaPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformComponentAndCheckerToThetaPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryComponentAndExtToThetaPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformComponentAndExtToThetaPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformComponentAndExtToThetaPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_T_reTheoryComponentAndCheckerToThetaPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformComponentAndCheckerToThetaPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl
    (provable_PA_reTheoryComponentAndCheckerToThetaPreservation T hRE)

theorem provable_T_reTheoryComponentAndExtToThetaPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformComponentAndExtToThetaPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl
    (provable_PA_reTheoryComponentAndExtToThetaPreservation T hRE)

end

end FailureOfComposition.NumericalExtensionTheta
