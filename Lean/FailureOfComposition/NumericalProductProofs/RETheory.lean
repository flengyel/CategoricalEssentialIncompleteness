/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProductProofs.Structural.Preservation

/-!
# Product proof maps for recursively enumerable theories

For an arithmetic theory `T` extending PA and equipped with recursively
enumerable axiom codes, this file selects the established theorem-stage test,
instantiates the product presentation and proof graph, and proves the exact
correspondence

`T ⊢ ∃ y, G_q(n,y)` if and only if `D(q,n)` has a numerical product proof.

The five proof transformations and their PA-internal preservation sentences
are then specialized to this same presentation.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open Arith.FixedFormulaNumeralSubstitution
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalProductProofs

open ProofSearch ConcreteEvaluator NumericalProofBridge TypedNearProduct

/-! ## Soundness in an extension of PA -/

theorem productLogicalAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (productTheoryPresentation w).syn.logicalAxiom.Holds s) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily s :=
  WeakerThan.pbl (productLogicalAxiom_meaning_provable w h)

theorem productTheoryAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {s : FormulaString}
    (h : (productTheoryPresentation w).ax.Holds s) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  apply extendedTheoryAxiom_meaning_provable_in T w hstage
  simpa [extendedTheoryPresentation, productTheoryPresentation] using h

theorem productProofLines_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ i, i < Ψ.length →
      LineJustified (productTheoryPresentation w) Ψ i) :
    ∀ i, i < Ψ.length →
      T ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, hcase⟩ := hj i hi
    rcases hcase with hlog | hax | ⟨j, hji, k, hki, himp⟩
    · exact productLogicalAxiom_meaning_provable_in T w hlog
    · exact productTheoryAxiom_meaning_provable_in T w hstage hax
    · have hjlen : j < Ψ.length := Nat.lt_trans hji hi
      have hklen : k < Ψ.length := Nat.lt_trans hki hi
      have hAntecedent := ih j hji hjlen
      have hImplication := ih k hki hklen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

private theorem product_reTheory_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem productIsProofList_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence} {s : FormulaString}
    (hΨ : IsProofList (productTheoryPresentation w) Ψ s) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := productProofLines_meaning_provable_in
    T w hstage hj (Ψ.length - 1) hidx
  rw [product_reTheory_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem productProof_T_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  productIsProofList_meaning_sound_in T w hstage hp

theorem productProof_T_definednessTag_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {p q n : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p
      (definednessTag q n)) :
    T ⊢ (eventualGraph (domainIndex q)).val/[n, n] := by
  have h := productProof_T_meaning_sound_in T w hstage hp
  simpa [definednessTag, rightInstanceCode, eventualFamily] using h

/-! ## The closed definedness equivalence -/

theorem pa_proves_definednessInstance_to_domain (q n : ℕ) :
    𝗣𝗔 ⊢ ((definednessFormula q).val/[n] 🡒
      (eventualGraph (domainIndex q)).val/[n, n]) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (definednessFormula q).val.Evalb
          ![(ORingStructure.numeral n : M)] →
        (eventualGraph (domainIndex q)).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] := by
    intro h
    rw [eventualGraph_domainIndex_eval]
    exact ⟨rfl, (definednessFormula_eval q _).mp h⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

theorem pa_proves_domain_to_definednessInstance (q n : ℕ) :
    𝗣𝗔 ⊢ ((eventualGraph (domainIndex q)).val/[n, n] 🡒
      (definednessFormula q).val/[n]) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (eventualGraph (domainIndex q)).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] →
        (definednessFormula q).val.Evalb
          ![(ORingStructure.numeral n : M)] := by
    intro h
    rw [eventualGraph_domainIndex_eval] at h
    exact (definednessFormula_eval q _).mpr h.2
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

/-! ## Generic exact correspondence for a supplied stage test -/

theorem theory_provable_definedness_iff_exists_product_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (henum : ∀ σ : ArithmeticSentence,
      T ⊢ σ ↔ ∃ s : ℕ, w (Encodable.encode σ) s = true)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    (q n : ℕ) :
    T ⊢ (definednessFormula q).val/[n] ↔
      ∃ p : ℕ, Proof_T (productTheoryPresentation w) p
        (definednessTag q n) := by
  constructor
  · intro h
    have hdom : T ⊢ (eventualGraph (domainIndex q)).val/[n, n] :=
      Entailment.mdp
        (WeakerThan.pbl (pa_proves_definednessInstance_to_domain q n)) h
    obtain ⟨p, hp⟩ :=
      (theory_provable_right_iff_exists_rightInstanceCode_proof_T
        T w henum hstage (domainIndex q) n n).mp hdom
    exact ⟨p, proof_T_extended_to_product w hp⟩
  · rintro ⟨p, hp⟩
    have hdom := productProof_T_definednessTag_sound_in T w hstage hp
    exact Entailment.mdp
      (WeakerThan.pbl (pa_proves_domain_to_definednessInstance q n)) hdom

/-! ## The selected product presentation for an r.e. theory -/

noncomputable def reTheoryProductTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    TheoryPresentation :=
  productTheoryPresentation (reTheoryStageWitness T hRE)

noncomputable def reTheoryProductPRTheoryPresentation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    PRTheoryPresentation :=
  productPRTheoryPresentation (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

noncomputable def reTheoryProductProofGraph
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 2 :=
  productProofGraph (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem reTheoryProductProofGraph_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (reTheoryProductProofGraph T hRE).val ↔
      Proof_T (reTheoryProductTheoryPresentation T hRE) p a := by
  exact productProofGraph_nat_iff
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE) p a

theorem reTheoryProductProof_T_meaning_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p a : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) := by
  exact productProof_T_meaning_sound_in T
    (reTheoryStageWitness T hRE)
    (reTheoryStageWitness_sound T hRE) hp

theorem reTheory_provable_definedness_iff_exists_product_proof_T
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (q n : ℕ) :
    T ⊢ (definednessFormula q).val/[n] ↔
      ∃ p : ℕ,
        Proof_T (reTheoryProductTheoryPresentation T hRE) p
          (definednessTag q n) := by
  exact theory_provable_definedness_iff_exists_product_proof_T T
    (reTheoryStageWitness T hRE)
    (reTheory_provable_iff_exists_stage T hRE)
    (reTheoryStageWitness_sound T hRE) q n

/-! ## The five selected proof transformations -/

theorem reTheoryProof_T_project0ToPair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (project0PairIndex q r) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (project0ToPair p q r n) (definednessTag (pairIndex q r) n) :=
  proof_T_project0ToPair (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_project1ToPair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (project1PairIndex q r) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (project1ToPair p q r n) (definednessTag (pairIndex q r) n) :=
  proof_T_project1ToPair (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_pairToLeft
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (pairIndex q r) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (pairToLeft p q r n) (definednessTag q n) :=
  proof_T_pairToLeft (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_pairToRight
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag (pairIndex q r) n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (pairToRight p q r n) (definednessTag r n) :=
  proof_T_pairToRight (reTheoryStageWitness T hRE) hp

theorem reTheoryProof_T_componentsToPair
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p h q r n : ℕ}
    (hp : Proof_T (reTheoryProductTheoryPresentation T hRE) p
      (definednessTag q n))
    (hh : Proof_T (reTheoryProductTheoryPresentation T hRE) h
      (definednessTag r n)) :
    Proof_T (reTheoryProductTheoryPresentation T hRE)
      (componentsToPair p h q r n)
      (definednessTag (pairIndex q r) n) :=
  proof_T_componentsToPair (reTheoryStageWitness T hRE) hp hh

/-! ## Selected internal preservation sentences -/

theorem provable_PA_reTheoryProject0ToPairPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformProject0ToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformProject0ToPairPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryProject1ToPairPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformProject1ToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformProject1ToPairPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryPairToLeftPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformPairToLeftPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformPairToLeftPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryPairToRightPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformPairToRightPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformPairToRightPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_PA_reTheoryComponentsToPairPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ uniformComponentsToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  provable_PA_uniformComponentsToPairPreservation
    (reTheoryStageWitness T hRE) (primrec_reTheoryStageWitness T hRE)

theorem provable_T_reTheoryProject0ToPairPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformProject0ToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryProject0ToPairPreservation T hRE)

theorem provable_T_reTheoryProject1ToPairPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformProject1ToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryProject1ToPairPreservation T hRE)

theorem provable_T_reTheoryPairToLeftPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformPairToLeftPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryPairToLeftPreservation T hRE)

theorem provable_T_reTheoryPairToRightPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformPairToRightPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryPairToRightPreservation T hRE)

theorem provable_T_reTheoryComponentsToPairPreservation
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    T ⊢ uniformComponentsToPairPreservation
      (reTheoryStageWitness T hRE)
      (primrec_reTheoryStageWitness T hRE) :=
  WeakerThan.pbl (provable_PA_reTheoryComponentsToPairPreservation T hRE)

end FailureOfComposition.NumericalProductProofs
