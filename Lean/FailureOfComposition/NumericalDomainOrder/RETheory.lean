/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalDomainOrder.Structural.Preservation
public import FailureOfComposition.NumericalProductProofs.RETheory

/-!
# Domain-order transfer for recursively enumerable theories

For an r.e.-axiomatized arithmetic theory extending PA, this module selects
the existing theorem-stage test, instantiates the domain-order presentation,
and proves exact equality-tag and right-instance-tag correspondences.  The
forward directions embed old proof codes; the reverse directions interpret
arbitrary proofs accepted by the new checker.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalDomainOrder

open ConcreteEvaluator NumericalProofBridge NumericalProductProofs ProofSearch

/-! ## Soundness in an extension of PA -/

theorem domainOrderLogicalAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (domainOrderTheoryPresentation w).syn.logicalAxiom.Holds x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x :=
  WeakerThan.pbl (domainOrderLogicalAxiom_meaning_provable w h)

theorem domainOrderTheoryAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (domainOrderTheoryPresentation w).ax.Holds x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply productTheoryAxiom_meaning_provable_in T w hstage
  simpa [productTheoryPresentation, domainOrderTheoryPresentation] using h

theorem domainOrderProofLines_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ j, j < Ψ.length →
      LineJustified (domainOrderTheoryPresentation w) Ψ j) :
    ∀ j, j < Ψ.length →
      T ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact domainOrderLogicalAxiom_meaning_provable_in T w hlog
    · exact domainOrderTheoryAxiom_meaning_provable_in T w hstage hax
    · have hulen : u < Ψ.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ψ.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

private theorem domainOrder_reTheory_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem domainOrderIsProofList_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence} {x : FormulaString}
    (hΨ : IsProofList (domainOrderTheoryPresentation w) Ψ x) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := domainOrderProofLines_meaning_provable_in
    T w hstage hj (Ψ.length - 1) hidx
  rw [domainOrder_reTheory_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem domainOrderProof_T_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (domainOrderTheoryPresentation w) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  domainOrderIsProofList_meaning_sound_in T w hstage hp

/-! ## The selected presentation -/

noncomputable def reTheoryDomainOrderTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    TheoryPresentation :=
  domainOrderTheoryPresentation (reTheoryStageWitness T hRE)

noncomputable def reTheoryDomainOrderPRTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    PRTheoryPresentation :=
  domainOrderPRTheoryPresentation (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

noncomputable def reTheoryDomainOrderProofGraph
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 2 :=
  domainOrderProofGraph (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem reTheoryDomainOrderProofGraph_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (reTheoryDomainOrderProofGraph T hRE).val ↔
      Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p a := by
  exact domainOrderProofGraph_nat_iff
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE) p a

theorem reTheoryDomainOrderProof_T_meaning_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p a : ℕ}
    (hp : Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  domainOrderProof_T_meaning_sound_in T
    (reTheoryStageWitness T hRE)
    (reTheoryStageWitness_sound T hRE) hp

theorem reTheoryDomainOrderProof_T_equalityCode_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r : ℕ}
    (hp : Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
      (equalityCode q r)) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  have h := reTheoryDomainOrderProof_T_meaning_sound T hRE hp
  simpa [equalityCode, firstSuccessFamily, eventualFamily] using h

theorem reTheoryDomainOrderProof_T_rightInstanceCode_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p r n m : ℕ}
    (hp : Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
      (rightInstanceCode r n m)) :
    T ⊢ (eventualGraph r).val/[n, m] := by
  have h := reTheoryDomainOrderProof_T_meaning_sound T hRE hp
  simpa [rightInstanceCode, eventualFamily] using h

/-! ## Exact endpoint correspondences for the new checker -/

theorem reTheory_provable_uniform_iff_exists_domainOrderProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (q r : ℕ) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) ↔
      ∃ p : ℕ, Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
        (equalityCode q r) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (reTheory_provable_uniform_iff_exists_equalityCode_proof_T
        T hRE q r).mp h
    exact ⟨p, proof_T_extended_to_domainOrder
      (reTheoryStageWitness T hRE) hp⟩
  · rintro ⟨p, hp⟩
    exact reTheoryDomainOrderProof_T_equalityCode_sound T hRE hp

theorem reTheory_provable_right_iff_exists_domainOrderProof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (r n m : ℕ) :
    T ⊢ (eventualGraph r).val/[n, m] ↔
      ∃ p : ℕ, Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
        (rightInstanceCode r n m) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ :=
      (reTheory_provable_right_iff_exists_rightInstanceCode_proof_T
        T hRE r n m).mp h
    exact ⟨p, proof_T_extended_to_domainOrder
      (reTheoryStageWitness T hRE) hp⟩
  · rintro ⟨p, hp⟩
    exact reTheoryDomainOrderProof_T_rightInstanceCode_sound T hRE hp

/-! ## Selected transformation and preservation theorem -/

theorem reTheoryProof_T_domainOrderTransfer
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {e p s r i : ℕ}
    (he : Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) e
      (equalityCode (UniformIndexQuotient.compIndex s r) r))
    (hp : Proof_T (reTheoryDomainOrderTheoryPresentation T hRE) p
      (rightInstanceCode r i i)) :
    Proof_T (reTheoryDomainOrderTheoryPresentation T hRE)
      (domainOrderTransfer e p s r i) (rightInstanceCode s i i) :=
  proof_T_domainOrderTransfer (reTheoryStageWitness T hRE) he hp

theorem provable_PA_reTheoryDomainOrderTransferPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformDomainOrderTransferPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformDomainOrderTransferPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_T_reTheoryDomainOrderTransferPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformDomainOrderTransferPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl
    (provable_PA_reTheoryDomainOrderTransferPreservation T hRE)

end FailureOfComposition.NumericalDomainOrder
