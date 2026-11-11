/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionComposition.Core
public import FailureOfComposition.NumericalExtensionProofs.Soundness

/-!
# PA meaning of the extension-composition schemes

Each scheme is proved for fixed external program indices and numerals in every
model of PA.  Intermediate computation values remain elements of the model.
In particular, no standard witness is extracted from an existential
definedness proof.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionComposition

open ConcreteEvaluator FiniteExtensionChecker NumericalDomainOrder
open NumericalExtensionProofs NumericalProofBridge NumericalProductProofs
open ProofSearch TypedNearProduct UniformIndexQuotient

noncomputable section

/-! ## Arithmetic meaning of the two schemes -/

set_option maxHeartbeats 5000000 in
-- The fixed-index first-success comparison expands to a large formula.
/-- Mixed equality and a computation of its eventual-graph endpoint imply the
domain tag at the first-success endpoint. -/
theorem provable_PA_meaning_projectionDefinedness
    (a b t i : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (projectionDefinednessAxiomString a b t i) := by
  simp only [projectionDefinednessAxiomString, formulaMeaning_impString,
    formulaMeaning_equalityString, formulaMeaning_rightInstanceString,
    definednessString, firstSuccessFamily, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hcomparison : ∀ x y : M,
      (firstSuccessGraph a).val.Evalb ![x, y] ↔
        (eventualGraph a).val.Evalb ![x, y] := by
    have h := consequence_iff.mp
      (Theory.Proof.sound (firstSuccessGraph_uniform_eventualGraph a))
      M inferInstance
    simpa [models_iff] using h
  have hsemantic :
      (∀ x y : M,
        (firstSuccessGraph a).val.Evalb ![x, y] ↔
          (eventualGraph b).val.Evalb ![x, y]) →
      (eventualGraph b).val.Evalb
          ![(ORingStructure.numeral t : M),
            (ORingStructure.numeral i : M)] →
      (eventualGraph (domainIndex a)).val.Evalb
          ![(ORingStructure.numeral t : M),
            (ORingStructure.numeral t : M)] := by
    intro heq hvalue
    have hfirst : (firstSuccessGraph a).val.Evalb
        ![(ORingStructure.numeral t : M),
          (ORingStructure.numeral i : M)] :=
      (heq _ _).mpr hvalue
    have heventual := (hcomparison _ _).mp hfirst
    rw [eventualGraph_domainIndex_eval]
    exact ⟨rfl, (ORingStructure.numeral i : M), heventual⟩
  simpa [models_iff, Semiformula.eval_substs, numeral_eq_natCast] using
    hsemantic

set_option maxHeartbeats 1000000 in
-- This proof combines the fixed-index comparison with pairing and composition.
/-- The two component computations and the checker fixed-point equality imply
the exact checker tag.  Functionality of the paired program identifies the
internal composition witness with the displayed data pair. -/
theorem provable_PA_meaning_componentValuesToChecker
    (q r t c i : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (componentValuesToCheckerAxiomString q r t c i) := by
  simp only [componentValuesToCheckerAxiomString,
    formulaMeaning_impString, formulaMeaning_equalityString,
    formulaMeaning_rightInstanceString, checkerInstanceString,
    firstSuccessFamily, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hcomparison : ∀ x y : M,
      (firstSuccessGraph (compIndex extensionCheckerIndex
        (pairIndex q r))).val.Evalb ![x, y] ↔
      (eventualGraph (compIndex extensionCheckerIndex
        (pairIndex q r))).val.Evalb ![x, y] := by
    have h := consequence_iff.mp
      (Theory.Proof.sound
        (firstSuccessGraph_uniform_eventualGraph
          (compIndex extensionCheckerIndex (pairIndex q r))))
      M inferInstance
    simpa [models_iff] using h
  have hpairNumeral :
      (ORingStructure.numeral (Nat.pair c i) : M) =
      pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
    simpa only [numeral_eq_natCast] using
      (coe_pair_eq_pair_coe (V := M) c i)
  have hsemantic :
      (∀ x y : M,
        (firstSuccessGraph (compIndex extensionCheckerIndex
          (pairIndex q r))).val.Evalb ![x, y] ↔
        (eventualGraph (pairIndex q r)).val.Evalb ![x, y]) →
      (eventualGraph q).val.Evalb
          ![(ORingStructure.numeral t : M),
            (ORingStructure.numeral c : M)] →
      (eventualGraph r).val.Evalb
          ![(ORingStructure.numeral t : M),
            (ORingStructure.numeral i : M)] →
      (eventualGraph extensionCheckerIndex).val.Evalb
          ![(ORingStructure.numeral (Nat.pair c i) : M),
            (ORingStructure.numeral (Nat.pair c i) : M)] := by
    intro heq hq hr
    have hp : (eventualGraph (pairIndex q r)).val.Evalb
        ![(ORingStructure.numeral t : M),
          (ORingStructure.numeral (Nat.pair c i) : M)] := by
      rw [hpairNumeral, eventualGraph_pairIndex_eval]
      exact ⟨ORingStructure.numeral c, ORingStructure.numeral i,
        hq, hr, rfl⟩
    have hfirst : (firstSuccessGraph (compIndex extensionCheckerIndex
        (pairIndex q r))).val.Evalb
        ![(ORingStructure.numeral t : M),
          (ORingStructure.numeral (Nat.pair c i) : M)] :=
      (heq _ _).mpr hp
    have hcomp := (hcomparison _ _).mp hfirst
    rw [eventualGraph_comp_eval] at hcomp
    obtain ⟨u, hpu, hku⟩ := hcomp
    have hu : u = (ORingStructure.numeral (Nat.pair c i) : M) :=
      eventualGraph_output_unique (pairIndex q r) _ u _ hpu hp
    simpa [hu] using hku
  simpa [models_iff, Semiformula.eval_substs,
    numeral_eq_natCast] using hsemantic

/-! ## Meaning soundness of the common checker -/

theorem extensionCompositionLogicalAxiom_meaning_provable
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds
      x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  change extensionCompositionLogicalAxiomTest x = true at h
  rw [extensionCompositionLogicalAxiomTest_eq_true_iff] at h
  rcases h with hfinite | hcomposition
  · apply finiteExtensionLogicalAxiom_meaning_provable w
    exact (finiteExtensionLogicalAxiomTest_eq_true_iff x).mpr hfinite
  · rw [extensionCompositionAxiomShape_iff] at hcomposition
    rcases hcomposition with ⟨a, b, t, i, rfl⟩ |
        ⟨q, r, t, c, i, rfl⟩
    · exact provable_PA_meaning_projectionDefinedness a b t i
    · exact provable_PA_meaning_componentValuesToChecker q r t c i

theorem extensionCompositionTheoryAxiom_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (extensionCompositionTheoryPresentation w).ax.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply finiteExtensionTheoryAxiom_meaning_provable w hstage
  simpa [finiteExtensionTheoryPresentation,
    extensionCompositionTheoryPresentation] using h

private theorem extensionComposition_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem extensionCompositionProofLines_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ j, j < Ψ.length →
      LineJustified (extensionCompositionTheoryPresentation w) Ψ j) :
    ∀ j, j < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact extensionCompositionLogicalAxiom_meaning_provable w hlog
    · exact extensionCompositionTheoryAxiom_meaning_provable w hstage hax
    · have hulen : u < Ψ.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ψ.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem extensionCompositionIsProofList_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence} {x : FormulaString}
    (hΨ : IsProofList (extensionCompositionTheoryPresentation w) Ψ x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := extensionCompositionProofLines_meaning_provable
    w hstage hj (Ψ.length - 1) hidx
  rw [extensionComposition_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem extensionCompositionProof_T_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (extensionCompositionTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extensionCompositionIsProofList_meaning_sound w hstage hp

end

end FailureOfComposition.NumericalExtensionComposition
