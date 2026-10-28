/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionProofs.Structural.Preservation
import FailureOfComposition.NumericalDomainOrder.RETheory

/-!
# Finite-extension proof conversion for recursively enumerable theories

For an r.e.-axiomatized arithmetic theory extending PA, this module selects
the theorem-stage test and proves exact proof-existence correspondences for
the checker tag `C(c,i)`, the zero-test graph tag `X(c,i)`, and the closed
formula `Ext(c,i)`.  Soundness is proved for every proof accepted by the new
presentation, including proofs using either added scheme.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionProofs

open ConcreteEvaluator FiniteExtensionChecker NumericalDomainOrder
open NumericalProofBridge NumericalProductProofs ProofSearch

noncomputable section

/-! ## Soundness in an extension of PA -/

theorem finiteExtensionLogicalAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (finiteExtensionTheoryPresentation w).syn.logicalAxiom.Holds x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x :=
  WeakerThan.pbl (finiteExtensionLogicalAxiom_meaning_provable w h)

theorem finiteExtensionTheoryAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (finiteExtensionTheoryPresentation w).ax.Holds x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply domainOrderTheoryAxiom_meaning_provable_in T w hstage
  simpa [domainOrderTheoryPresentation,
    finiteExtensionTheoryPresentation] using h

theorem finiteExtensionProofLines_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ j, j < Ψ.length →
      LineJustified (finiteExtensionTheoryPresentation w) Ψ j) :
    ∀ j, j < Ψ.length →
      T ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact finiteExtensionLogicalAxiom_meaning_provable_in T w hlog
    · exact finiteExtensionTheoryAxiom_meaning_provable_in T w hstage hax
    · have hulen : u < Ψ.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ψ.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

private theorem finiteExtension_reTheory_getD_last_eq
    (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem finiteExtensionIsProofList_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence} {x : FormulaString}
    (hΨ : IsProofList (finiteExtensionTheoryPresentation w) Ψ x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := finiteExtensionProofLines_meaning_provable_in
    T w hstage hj (Ψ.length - 1) hidx
  rw [finiteExtension_reTheory_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem finiteExtensionProof_T_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (finiteExtensionTheoryPresentation w) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  finiteExtensionIsProofList_meaning_sound_in T w hstage hp

/-! ## The selected presentation -/

def reTheoryFiniteExtensionTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    TheoryPresentation :=
  finiteExtensionTheoryPresentation (reTheoryStageWitness T hRE)

def reTheoryFiniteExtensionPRTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    PRTheoryPresentation :=
  finiteExtensionPRTheoryPresentation (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

def reTheoryFiniteExtensionProofGraph
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 2 :=
  finiteExtensionProofGraph (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem reTheoryFiniteExtensionProofGraph_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (reTheoryFiniteExtensionProofGraph T hRE).val ↔
      Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p a := by
  exact finiteExtensionProofGraph_nat_iff
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE) p a

theorem reTheoryFiniteExtensionProof_T_meaning_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p a : ℕ}
    (hp : Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  finiteExtensionProof_T_meaning_sound_in T
    (reTheoryStageWitness T hRE)
    (reTheoryStageWitness_sound T hRE) hp

theorem reTheoryFiniteExtensionProof_T_rightInstanceCode_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p r n m : ℕ}
    (hp : Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
      (rightInstanceCode r n m)) :
    T ⊢ (eventualGraph r).val/[n, m] := by
  have h := reTheoryFiniteExtensionProof_T_meaning_sound T hRE hp
  simpa [rightInstanceCode, eventualFamily] using h

/-! ## Exact proof-existence correspondences -/

theorem reTheory_provable_right_iff_exists_finiteExtensionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (r n m : ℕ) :
    T ⊢ (eventualGraph r).val/[n, m] ↔
      ∃ p : ℕ,
        Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
          (rightInstanceCode r n m) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (reTheory_provable_right_iff_exists_rightInstanceCode_proof_T
        T hRE r n m).mp h
    exact ⟨p, proof_T_extended_to_finiteExtension
      (reTheoryStageWitness T hRE) hp⟩
  · rintro ⟨p, hp⟩
    exact reTheoryFiniteExtensionProof_T_rightInstanceCode_sound T hRE hp

theorem reTheory_provable_checker_iff_exists_finiteExtensionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ (eventualGraph extensionCheckerIndex).val/[
        Nat.pair c i, Nat.pair c i] ↔
      ∃ p : ℕ,
        Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
          (checkerInstanceCode c i) := by
  simpa using
    reTheory_provable_right_iff_exists_finiteExtensionProof_T
      T hRE extensionCheckerIndex (Nat.pair c i) (Nat.pair c i)

theorem reTheory_provable_zeroTest_iff_exists_finiteExtensionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ (eventualGraph zeroTestIndex).val/[Nat.pair c i, (0 : ℕ)] ↔
      ∃ p : ℕ,
        Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
          (extensionInstanceCode c i) := by
  simpa using
    reTheory_provable_right_iff_exists_finiteExtensionProof_T
      T hRE zeroTestIndex (Nat.pair c i) (0 : ℕ)

theorem reTheory_provable_extension_iff_exists_checkerProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ extensionFormula.val/[c, i] ↔
      ∃ p : ℕ,
        Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
          (checkerInstanceCode c i) :=
  (proves_checker_iff_extension T c i).symm.trans
    (reTheory_provable_checker_iff_exists_finiteExtensionProof_T
      T hRE c i)

theorem reTheory_provable_extension_iff_exists_extensionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ extensionFormula.val/[c, i] ↔
      ∃ p : ℕ,
        Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
          (extensionInstanceCode c i) :=
  (proves_zeroTest_iff_extension T c i).symm.trans
    (reTheory_provable_zeroTest_iff_exists_finiteExtensionProof_T
      T hRE c i)

/-! ## Selected conversions and internal preservation -/

theorem reTheoryProof_T_checkerToExt
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p c i : ℕ}
    (hp : Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
      (checkerInstanceCode c i)) :
    Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE)
      (checkerToExt p c i) (extensionInstanceCode c i) :=
  proof_T_checkerToExt (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_extToChecker
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p c i : ℕ}
    (hp : Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
      (extensionInstanceCode c i)) :
    Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE)
      (extToChecker p c i) (checkerInstanceCode c i) :=
  proof_T_extToChecker (reTheoryStageWitness T hRE) hp

theorem provable_PA_reTheoryCheckerToExtPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformCheckerToExtPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformCheckerToExtPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryExtToCheckerPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformExtToCheckerPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformExtToCheckerPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_T_reTheoryCheckerToExtPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformCheckerToExtPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryCheckerToExtPreservation T hRE)

theorem provable_T_reTheoryExtToCheckerPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformExtToCheckerPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryExtToCheckerPreservation T hRE)

/-! ## Closed numerical applications -/

theorem reTheory_empty_checkerProof
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) (i : ℕ) :
    ∃ p : ℕ,
      Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
        (checkerInstanceCode 0 i) :=
  (reTheory_provable_extension_iff_exists_checkerProof_T T hRE 0 i).mp
    (proves_extensionFormula_zero T i)

/-- Code one and the identity program provide a concrete proof code, and both
conversions produce proof codes at their advertised endpoints. -/
theorem reTheory_one_identity_conversion_evidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    ∃ p : ℕ,
      Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE) p
          (checkerInstanceCode 1 Kleene.identityIndex) ∧
      Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE)
          (checkerToExt p 1 Kleene.identityIndex)
          (extensionInstanceCode 1 Kleene.identityIndex) ∧
      Proof_T (reTheoryFiniteExtensionTheoryPresentation T hRE)
          (extToChecker (checkerToExt p 1 Kleene.identityIndex)
            1 Kleene.identityIndex)
          (checkerInstanceCode 1 Kleene.identityIndex) := by
  have hext : T ⊢ extensionFormula.val/[(1 : ℕ), Kleene.identityIndex] :=
    WeakerThan.pbl pa_proves_extensionFormula_one_identity
  obtain ⟨p, hp⟩ :=
    (reTheory_provable_extension_iff_exists_checkerProof_T
      T hRE 1 Kleene.identityIndex).mp hext
  have hforward := reTheoryProof_T_checkerToExt T hRE hp
  exact ⟨p, hp, hforward,
    reTheoryProof_T_extToChecker T hRE hforward⟩

end

end FailureOfComposition.NumericalExtensionProofs
