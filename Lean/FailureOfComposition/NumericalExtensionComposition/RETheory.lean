/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionComposition.Soundness
import FailureOfComposition.NumericalExtensionComposition.Structural.Preservation
import FailureOfComposition.NumericalExtensionProofs.RETheory

/-!
# Composed B1(7) proof maps for recursively enumerable theories

For a recursively enumerable arithmetic theory extending PA, this file fixes
one common presentation, specializes the four numerical transformations, and
records exact proof-existence correspondences for the mixed equality tag
`E`, computation tag `R`, domain tag `D`, checker tag `C`, and zero-test tag
`X`.  The closed preservation sentences are proved first in PA and then
lifted to the selected theory.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionComposition

open ConcreteEvaluator FiniteExtensionChecker NumericalDomainOrder
open NumericalExtensionProofs NumericalProofBridge NumericalProductProofs
open ProofSearch TypedNearProduct

noncomputable section

/-! ## Soundness in an extension of PA -/

theorem extensionCompositionLogicalAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds
      x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x :=
  WeakerThan.pbl (extensionCompositionLogicalAxiom_meaning_provable w h)

theorem extensionCompositionTheoryAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (extensionCompositionTheoryPresentation w).ax.Holds x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply finiteExtensionTheoryAxiom_meaning_provable_in T w hstage
  simpa [finiteExtensionTheoryPresentation,
    extensionCompositionTheoryPresentation] using h

theorem extensionCompositionProofLines_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ps : ProofSequence}
    (hj : ∀ j, j < Ps.length →
      LineJustified (extensionCompositionTheoryPresentation w) Ps j) :
    ∀ j, j < Ps.length →
      T ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ps.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact extensionCompositionLogicalAxiom_meaning_provable_in
        T w hlog
    · exact extensionCompositionTheoryAxiom_meaning_provable_in
        T w hstage hax
    · have hulen : u < Ps.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ps.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

private theorem extensionComposition_reTheory_getD_last_eq
    (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem extensionCompositionIsProofList_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ps : ProofSequence} {x : FormulaString}
    (hPs : IsProofList (extensionCompositionTheoryPresentation w) Ps x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hPs
  have hidx : Ps.length - 1 < Ps.length := by
    have : 0 < Ps.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := extensionCompositionProofLines_meaning_provable_in
    T w hstage hj (Ps.length - 1) hidx
  rw [extensionComposition_reTheory_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem extensionCompositionProof_T_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extensionCompositionIsProofList_meaning_sound_in T w hstage hp

/-! ## The selected common presentation -/

def reTheoryExtensionCompositionTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    TheoryPresentation :=
  extensionCompositionTheoryPresentation (reTheoryStageWitness T hRE)

def reTheoryExtensionCompositionPRTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    PRTheoryPresentation :=
  extensionCompositionPRTheoryPresentation (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

def reTheoryExtensionCompositionProofGraph
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 2 :=
  extensionCompositionProofGraph (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem reTheoryExtensionCompositionProofGraph_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (reTheoryExtensionCompositionProofGraph T hRE).val ↔
      Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p a :=
  extensionCompositionProofGraph_nat_iff
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE) p a

theorem reTheoryExtensionCompositionProof_T_meaning_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p a : ℕ}
    (hp : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extensionCompositionProof_T_meaning_sound_in T
    (reTheoryStageWitness T hRE) (reTheoryStageWitness_sound T hRE) hp

theorem reTheoryExtensionCompositionProof_T_equalityCode_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r : ℕ}
    (hp : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
      (equalityCode q r)) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  have h := reTheoryExtensionCompositionProof_T_meaning_sound T hRE hp
  simpa [equalityCode, firstSuccessFamily, eventualFamily] using h

theorem reTheoryExtensionCompositionProof_T_rightInstanceCode_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p r n m : ℕ}
    (hp : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
      (rightInstanceCode r n m)) :
    T ⊢ (eventualGraph r).val/[n, m] := by
  have h := reTheoryExtensionCompositionProof_T_meaning_sound T hRE hp
  simpa [rightInstanceCode, eventualFamily] using h

/-! ## Exact endpoint correspondences -/

theorem reTheory_provable_uniform_iff_exists_extensionCompositionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (q r : ℕ) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (equalityCode q r) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (reTheory_provable_uniform_iff_exists_domainOrderProof_T
        T hRE q r).mp h
    exact ⟨p, proof_T_finiteExtension_to_extensionComposition
      (reTheoryStageWitness T hRE)
      (proof_T_domainOrder_to_finiteExtension
        (reTheoryStageWitness T hRE) hp)⟩
  · rintro ⟨p, hp⟩
    exact reTheoryExtensionCompositionProof_T_equalityCode_sound T hRE hp

theorem reTheory_provable_right_iff_exists_extensionCompositionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (r n m : ℕ) :
    T ⊢ (eventualGraph r).val/[n, m] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (rightInstanceCode r n m) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (reTheory_provable_right_iff_exists_finiteExtensionProof_T
        T hRE r n m).mp h
    exact ⟨p, proof_T_finiteExtension_to_extensionComposition
      (reTheoryStageWitness T hRE) hp⟩
  · rintro ⟨p, hp⟩
    exact reTheoryExtensionCompositionProof_T_rightInstanceCode_sound
      T hRE hp

theorem reTheory_provable_definedness_iff_exists_extensionCompositionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (q n : ℕ) :
    T ⊢ (definednessFormula q).val/[n] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (definednessTag q n) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (reTheory_provable_definedness_iff_exists_product_proof_T
        T hRE q n).mp h
    exact ⟨p, proof_T_product_to_extensionComposition
      (reTheoryStageWitness T hRE) hp⟩
  · rintro ⟨p, hp⟩
    have hdom := reTheoryExtensionCompositionProof_T_rightInstanceCode_sound
      T hRE hp
    exact Entailment.mdp
      (WeakerThan.pbl (pa_proves_domain_to_definednessInstance q n)) hdom

theorem reTheory_provable_checker_iff_exists_extensionCompositionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ (eventualGraph extensionCheckerIndex).val/[
        Nat.pair c i, Nat.pair c i] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (checkerInstanceCode c i) := by
  simpa using
    reTheory_provable_right_iff_exists_extensionCompositionProof_T
      T hRE extensionCheckerIndex (Nat.pair c i) (Nat.pair c i)

theorem reTheory_provable_zeroTest_iff_exists_extensionCompositionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ (eventualGraph zeroTestIndex).val/[Nat.pair c i, (0 : ℕ)] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (extensionInstanceCode c i) := by
  simpa using
    reTheory_provable_right_iff_exists_extensionCompositionProof_T
      T hRE zeroTestIndex (Nat.pair c i) 0

theorem reTheory_provable_extension_iff_exists_checkerCompositionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ extensionFormula.val/[c, i] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (checkerInstanceCode c i) :=
  (proves_checker_iff_extension T c i).symm.trans
    (reTheory_provable_checker_iff_exists_extensionCompositionProof_T
      T hRE c i)

theorem reTheory_provable_extension_iff_exists_extensionCompositionProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (c i : ℕ) :
    T ⊢ extensionFormula.val/[c, i] ↔
      ∃ p : ℕ, Proof_T
        (reTheoryExtensionCompositionTheoryPresentation T hRE) p
        (extensionInstanceCode c i) :=
  (proves_zeroTest_iff_extension T c i).symm.trans
    (reTheory_provable_zeroTest_iff_exists_extensionCompositionProof_T
      T hRE c i)

/-! ## Selected transformations -/

theorem reTheoryProof_T_projectionEqualityToPair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {u p q r t i : ℕ}
    (hu : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) u
      (equalityCode (project1PairIndex q r) r))
    (hp : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
      (rightInstanceCode r t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (projectionEqualityToPair u p q r t i)
      (definednessTag (pairIndex q r) t) :=
  proof_T_projectionEqualityToPair (reTheoryStageWitness T hRE) hu hp

theorem reTheoryProof_T_projectionEqualityToLeft
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {u p q r t i : ℕ}
    (hu : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) u
      (equalityCode (project1PairIndex q r) r))
    (hp : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) p
      (rightInstanceCode r t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (projectionEqualityToLeft u p q r t i) (definednessTag q t) :=
  proof_T_projectionEqualityToLeft (reTheoryStageWitness T hRE) hu hp

theorem reTheoryProof_T_componentValuesToChecker
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {v a b q r t c i : ℕ}
    (hv : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) v
      (equalityCode
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          (pairIndex q r)) (pairIndex q r)))
    (ha : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) a
      (rightInstanceCode q t c))
    (hb : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) b
      (rightInstanceCode r t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (componentValuesToChecker v a b q r t c i)
      (checkerInstanceCode c i) :=
  proof_T_componentValuesToChecker (reTheoryStageWitness T hRE) hv ha hb

theorem reTheoryProof_T_componentValuesToExt
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {v a b q r t c i : ℕ}
    (hv : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) v
      (equalityCode
        (UniformIndexQuotient.compIndex extensionCheckerIndex
          (pairIndex q r)) (pairIndex q r)))
    (ha : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) a
      (rightInstanceCode q t c))
    (hb : Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE) b
      (rightInstanceCode r t i)) :
    Proof_T (reTheoryExtensionCompositionTheoryPresentation T hRE)
      (componentValuesToExt v a b q r t c i)
      (extensionInstanceCode c i) :=
  proof_T_componentValuesToExt (reTheoryStageWitness T hRE) hv ha hb

/-! ## Selected internal preservation sentences -/

theorem provable_PA_reTheoryProjectionEqualityToPairPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformProjectionEqualityToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformProjectionEqualityToPairPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryProjectionEqualityToLeftPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformProjectionEqualityToLeftPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformProjectionEqualityToLeftPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryComponentValuesToCheckerPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformComponentValuesToCheckerPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformComponentValuesToCheckerPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryComponentValuesToExtPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformComponentValuesToExtPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformComponentValuesToExtPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_T_reTheoryProjectionEqualityToPairPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformProjectionEqualityToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl
    (provable_PA_reTheoryProjectionEqualityToPairPreservation T hRE)

theorem provable_T_reTheoryProjectionEqualityToLeftPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformProjectionEqualityToLeftPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl
    (provable_PA_reTheoryProjectionEqualityToLeftPreservation T hRE)

theorem provable_T_reTheoryComponentValuesToCheckerPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformComponentValuesToCheckerPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl
    (provable_PA_reTheoryComponentValuesToCheckerPreservation T hRE)

theorem provable_T_reTheoryComponentValuesToExtPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformComponentValuesToExtPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl
    (provable_PA_reTheoryComponentValuesToExtPreservation T hRE)

end

end FailureOfComposition.NumericalExtensionComposition
