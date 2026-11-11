/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionProofs.Core
public import FailureOfComposition.NumericalDomainOrder.Soundness

/-!
# Meaning soundness of the finite-extension proof presentation

The two new schemes compare graph tags at the exact checker and zero-test
endpoints.  Their PA meaning follows from the independently proved graph laws;
the zero-test tag is not treated as a native code of `extensionFormula`.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionProofs

open ConcreteEvaluator FiniteExtensionChecker NumericalDomainOrder
open NumericalProofBridge ProofSearch

noncomputable section

/-! ## Arithmetic meaning of the two schemes -/

theorem provable_PA_meaning_checkerToExtension (c i : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (checkerToExtensionAxiomString c i) := by
  simp only [checkerToExtensionAxiomString, formulaMeaning_impString,
    checkerInstanceString, extensionInstanceString,
    formulaMeaning_rightInstanceString, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hu : (ORingStructure.numeral (Nat.pair c i) : M) =
      pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
    simpa only [numeral_eq_natCast] using
      (coe_pair_eq_pair_coe (V := M) c i)
  have hsemantic :
      (eventualGraph extensionCheckerIndex).val.Evalb
          ![(ORingStructure.numeral (Nat.pair c i) : M),
            (ORingStructure.numeral (Nat.pair c i) : M)] →
        (eventualGraph zeroTestIndex).val.Evalb
          ![(ORingStructure.numeral (Nat.pair c i) : M), (0 : M)] := by
    intro hcheck
    rw [hu, eventualGraph_extensionCheckerIndex_pair_eval] at hcheck
    rw [hu, eventualGraph_zeroTestIndex_pair_eval]
    exact ⟨rfl, hcheck.2⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

theorem provable_PA_meaning_extensionToChecker (c i : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (extensionToCheckerAxiomString c i) := by
  simp only [extensionToCheckerAxiomString, formulaMeaning_impString,
    checkerInstanceString, extensionInstanceString,
    formulaMeaning_rightInstanceString, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hu : (ORingStructure.numeral (Nat.pair c i) : M) =
      pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
    simpa only [numeral_eq_natCast] using
      (coe_pair_eq_pair_coe (V := M) c i)
  have hsemantic :
      (eventualGraph zeroTestIndex).val.Evalb
          ![(ORingStructure.numeral (Nat.pair c i) : M), (0 : M)] →
        (eventualGraph extensionCheckerIndex).val.Evalb
          ![(ORingStructure.numeral (Nat.pair c i) : M),
            (ORingStructure.numeral (Nat.pair c i) : M)] := by
    intro hext
    rw [hu, eventualGraph_zeroTestIndex_pair_eval] at hext
    rw [hu, eventualGraph_extensionCheckerIndex_pair_eval]
    exact ⟨rfl, hext.2⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

/-! ## Soundness of all proofs accepted by the new checker -/

theorem finiteExtensionLogicalAxiom_meaning_provable
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (finiteExtensionTheoryPresentation w).syn.logicalAxiom.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  change finiteExtensionLogicalAxiomTest x = true at h
  rw [finiteExtensionLogicalAxiomTest_eq_true_iff] at h
  rcases h with hdomain | hextension
  · apply domainOrderLogicalAxiom_meaning_provable w
    exact (domainOrderLogicalAxiomTest_eq_true_iff x).mpr hdomain
  · rw [extensionAxiomShape_iff] at hextension
    rcases hextension with ⟨c, i, rfl⟩ | ⟨c, i, rfl⟩
    · exact provable_PA_meaning_checkerToExtension c i
    · exact provable_PA_meaning_extensionToChecker c i

theorem finiteExtensionTheoryAxiom_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (finiteExtensionTheoryPresentation w).ax.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply domainOrderTheoryAxiom_meaning_provable w hstage
  simpa [domainOrderTheoryPresentation,
    finiteExtensionTheoryPresentation] using h

private theorem finiteExtension_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem finiteExtensionProofLines_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ j, j < Ψ.length →
      LineJustified (finiteExtensionTheoryPresentation w) Ψ j) :
    ∀ j, j < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact finiteExtensionLogicalAxiom_meaning_provable w hlog
    · exact finiteExtensionTheoryAxiom_meaning_provable w hstage hax
    · have hulen : u < Ψ.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ψ.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem finiteExtensionIsProofList_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence} {x : FormulaString}
    (hΨ : IsProofList (finiteExtensionTheoryPresentation w) Ψ x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := finiteExtensionProofLines_meaning_provable
    w hstage hj (Ψ.length - 1) hidx
  rw [finiteExtension_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem finiteExtensionProof_T_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (finiteExtensionTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  finiteExtensionIsProofList_meaning_sound w hstage hp

end

end FailureOfComposition.NumericalExtensionProofs
