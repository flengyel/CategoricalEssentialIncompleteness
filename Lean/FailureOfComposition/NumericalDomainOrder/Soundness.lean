/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalDomainOrder.Core
public import FailureOfComposition.NumericalProductProofs.Soundness

/-!
# Soundness of numerical domain-order transfer

The added scheme is proved in every model of PA for each fixed triple of
standard program indices and numeral.  The proof keeps the first-success and
eventual graphs distinct: it first applies their established PA comparison at
the composite index and then uses composition and functionality of the
eventual graph.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalDomainOrder

open ConcreteEvaluator NumericalProofBridge NumericalProductProofs ProofSearch
open UniformIndexQuotient

/-! ## Arithmetic meaning of the scheme -/

set_option maxHeartbeats 1000000 in
-- The fixed-index first-success comparison has a large elaborated formula.
/-- Every fixed standard instance of the domain-order implication is a PA
theorem.  The intermediate computation value is internal to the PA model. -/
theorem provable_PA_meaning_domainOrder (s r i : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (domainOrderAxiomString s r i) := by
  simp only [domainOrderAxiomString, formulaMeaning_impString,
    formulaMeaning_equalityString, formulaMeaning_rightInstanceString,
    firstSuccessFamily, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hsemantic :
      (∀ x y : M,
        (firstSuccessGraph (compIndex s r)).val.Evalb ![x, y] ↔
          (eventualGraph r).val.Evalb ![x, y]) →
      (eventualGraph r).val.Evalb
          ![(ORingStructure.numeral i : M),
            (ORingStructure.numeral i : M)] →
      (eventualGraph s).val.Evalb
          ![(ORingStructure.numeral i : M),
            (ORingStructure.numeral i : M)] := by
    intro heq hrii
    have hfirst :
        (firstSuccessGraph (compIndex s r)).val.Evalb
          ![(ORingStructure.numeral i : M),
            (ORingStructure.numeral i : M)] :=
      (heq _ _).mpr hrii
    have hcomparison : ∀ x y : M,
        (firstSuccessGraph (compIndex s r)).val.Evalb ![x, y] ↔
          (eventualGraph (compIndex s r)).val.Evalb ![x, y] := by
      have h := consequence_iff.mp
        (Theory.Proof.sound
          (firstSuccessGraph_uniform_eventualGraph (compIndex s r)))
          M inferInstance
      simpa [models_iff] using h
    have hcomp :
        (eventualGraph (compIndex s r)).val.Evalb
          ![(ORingStructure.numeral i : M),
            (ORingStructure.numeral i : M)] :=
      (hcomparison _ _).mp hfirst
    rw [eventualGraph_comp_eval] at hcomp
    obtain ⟨z, hriz, hszi⟩ := hcomp
    have hz : z = (ORingStructure.numeral i : M) :=
      eventualGraph_output_unique r _ z _ hriz hrii
    simpa [hz] using hszi
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

/-! ## Soundness of the extended presentation -/

theorem domainOrderLogicalAxiom_meaning_provable
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (domainOrderTheoryPresentation w).syn.logicalAxiom.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  change domainOrderLogicalAxiomTest x = true at h
  rw [domainOrderLogicalAxiomTest_eq_true_iff] at h
  rcases h with hproduct | horder
  · apply productLogicalAxiom_meaning_provable w
    exact (productLogicalAxiomTest_eq_true_iff x).mpr hproduct
  · rw [domainOrderAxiomShape_iff] at horder
    obtain ⟨s, r, i, rfl⟩ := horder
    exact provable_PA_meaning_domainOrder s r i

theorem domainOrderTheoryAxiom_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (domainOrderTheoryPresentation w).ax.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply productTheoryAxiom_meaning_provable w hstage
  simpa [productTheoryPresentation, domainOrderTheoryPresentation] using h

private theorem domainOrder_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem domainOrderProofLines_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ j, j < Ψ.length →
      LineJustified (domainOrderTheoryPresentation w) Ψ j) :
    ∀ j, j < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact domainOrderLogicalAxiom_meaning_provable w hlog
    · exact domainOrderTheoryAxiom_meaning_provable w hstage hax
    · have hulen : u < Ψ.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ψ.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem domainOrderIsProofList_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence} {x : FormulaString}
    (hΨ : IsProofList (domainOrderTheoryPresentation w) Ψ x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := domainOrderProofLines_meaning_provable w hstage hj
    (Ψ.length - 1) hidx
  rw [domainOrder_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem domainOrderProof_T_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (domainOrderTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  domainOrderIsProofList_meaning_sound w hstage hp

end FailureOfComposition.NumericalDomainOrder
