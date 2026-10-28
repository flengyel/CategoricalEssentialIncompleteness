/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProductProofs.Core

/-!
# Soundness of the numerical product proof rules

The five added logical-axiom schemes express exactly the definedness laws of
the partial pairing program.  This file proves their meaning in every model of
PA and lifts that result through the numerical proof calculus.
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

open ProofSearch ConcreteEvaluator
open NumericalProofBridge TypedNearProduct TypedProgramCategory
open UniformIndexQuotient

/-! ## Meaning of the five schemes -/

theorem provable_PA_meaning_project0ToPair (q r n : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (project0ToPairAxiomString q r n) := by
  simp only [project0ToPairAxiomString, formulaMeaning_impString,
    definednessString, formulaMeaning_rightInstanceString,
    eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (eventualGraph (domainIndex (project0PairIndex q r))).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] →
        (eventualGraph (domainIndex (pairIndex q r))).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] := by
    intro h
    rw [eventualGraph_domainIndex_eval] at h ⊢
    obtain ⟨hdiag, z, hz⟩ := h
    refine ⟨hdiag, ?_⟩
    rw [project0PairIndex, eventualGraph_comp_eval] at hz
    obtain ⟨u, hpair, -⟩ := hz
    exact ⟨u, hpair⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

theorem provable_PA_meaning_project1ToPair (q r n : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (project1ToPairAxiomString q r n) := by
  simp only [project1ToPairAxiomString, formulaMeaning_impString,
    definednessString, formulaMeaning_rightInstanceString,
    eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (eventualGraph (domainIndex (project1PairIndex q r))).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] →
        (eventualGraph (domainIndex (pairIndex q r))).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] := by
    intro h
    rw [eventualGraph_domainIndex_eval] at h ⊢
    obtain ⟨hdiag, z, hz⟩ := h
    refine ⟨hdiag, ?_⟩
    rw [project1PairIndex, eventualGraph_comp_eval] at hz
    obtain ⟨u, hpair, -⟩ := hz
    exact ⟨u, hpair⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

theorem provable_PA_meaning_pairToLeft (q r n : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (pairToLeftAxiomString q r n) := by
  simp only [pairToLeftAxiomString, formulaMeaning_impString,
    definednessString, formulaMeaning_rightInstanceString,
    eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (eventualGraph (domainIndex (pairIndex q r))).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] →
        (eventualGraph (domainIndex q)).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] := by
    intro h
    rw [eventualGraph_domainIndex_eval] at h ⊢
    obtain ⟨hdiag, z, hz⟩ := h
    refine ⟨hdiag, ?_⟩
    rw [eventualGraph_pairIndex_eval] at hz
    obtain ⟨y, w, hq, -, -⟩ := hz
    exact ⟨y, hq⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

theorem provable_PA_meaning_pairToRight (q r n : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (pairToRightAxiomString q r n) := by
  simp only [pairToRightAxiomString, formulaMeaning_impString,
    definednessString, formulaMeaning_rightInstanceString,
    eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (eventualGraph (domainIndex (pairIndex q r))).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] →
        (eventualGraph (domainIndex r)).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] := by
    intro h
    rw [eventualGraph_domainIndex_eval] at h ⊢
    obtain ⟨hdiag, z, hz⟩ := h
    refine ⟨hdiag, ?_⟩
    rw [eventualGraph_pairIndex_eval] at hz
    obtain ⟨y, w, -, hr, -⟩ := hz
    exact ⟨w, hr⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

theorem provable_PA_meaning_componentsToPair (q r n : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (componentsToPairAxiomString q r n) := by
  simp only [componentsToPairAxiomString, formulaMeaning_impString,
    definednessString, formulaMeaning_rightInstanceString,
    eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (eventualGraph (domainIndex q)).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] →
        (eventualGraph (domainIndex r)).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] →
        (eventualGraph (domainIndex (pairIndex q r))).val.Evalb
          ![(ORingStructure.numeral n : M),
            (ORingStructure.numeral n : M)] := by
    intro hq hr
    rw [eventualGraph_domainIndex_eval] at hq hr ⊢
    obtain ⟨hdiag, y, hqy⟩ := hq
    obtain ⟨-, w, hrw⟩ := hr
    refine ⟨hdiag, pair y w, ?_⟩
    rw [eventualGraph_pairIndex_eval]
    exact ⟨y, w, hqy, hrw, rfl⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

/-! ## Soundness of the extended proof presentation -/

theorem productLogicalAxiom_meaning_provable
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (productTheoryPresentation w).syn.logicalAxiom.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  change productLogicalAxiomTest s = true at h
  rw [productLogicalAxiomTest_eq_true_iff] at h
  rcases h with hold | hproduct
  · apply extendedLogicalAxiom_meaning_provable w
    exact (extendedLogicalAxiomTest_eq_true_iff s).mpr hold
  · rw [productAxiomShape_iff] at hproduct
    rcases hproduct with ⟨q, r, n, rfl⟩ |
        ⟨q, r, n, rfl⟩ | ⟨q, r, n, rfl⟩ |
        ⟨q, r, n, rfl⟩ | ⟨q, r, n, rfl⟩
    · exact provable_PA_meaning_project0ToPair q r n
    · exact provable_PA_meaning_project1ToPair q r n
    · exact provable_PA_meaning_pairToLeft q r n
    · exact provable_PA_meaning_pairToRight q r n
    · exact provable_PA_meaning_componentsToPair q r n

theorem productTheoryAxiom_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {s : FormulaString}
    (h : (productTheoryPresentation w).ax.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  apply extendedTheoryAxiom_meaning_provable w hstage
  simpa [extendedTheoryPresentation, productTheoryPresentation] using h

private theorem product_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem productProofLines_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ i, i < Ψ.length →
      LineJustified (productTheoryPresentation w) Ψ i) :
    ∀ i, i < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, hcase⟩ := hj i hi
    rcases hcase with hlog | hax | ⟨j, hji, k, hki, himp⟩
    · exact productLogicalAxiom_meaning_provable w hlog
    · exact productTheoryAxiom_meaning_provable w hstage hax
    · have hjlen : j < Ψ.length := Nat.lt_trans hji hi
      have hklen : k < Ψ.length := Nat.lt_trans hki hi
      have hAntecedent := ih j hji hjlen
      have hImplication := ih k hki hklen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem productIsProofList_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence} {s : FormulaString}
    (hΨ : IsProofList (productTheoryPresentation w) Ψ s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := productProofLines_meaning_provable w hstage hj
    (Ψ.length - 1) hidx
  rw [product_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem productProof_T_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (productTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  productIsProofList_meaning_sound w hstage hp

end FailureOfComposition.NumericalProductProofs
