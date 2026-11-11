/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.PrfEqTransportRepair.Core

/-!
# Soundness and standard compatibility of the transport repair

The added direct scheme is a theorem of PA under the intended interpretation
of equality tags.  The proof uses the PA theorem equating the first-success
and eventual graphs at the middle index.  Consequently every repair proof has
its intended arithmetic meaning.  At equality endpoints this gives a
standard, existential translation back to the production checker; it does not
construct a primitive-recursive proof-code backtranslation.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.PrfEqTransportRepair

open ConcreteEvaluator NumericalProofBridge ProofSearch
open UniformIndexQuotient

/-! ## Meaning of the added scheme -/

theorem provable_PA_meaning_transportAxiom (y y' d : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (transportAxiomString y y' d) := by
  simp only [transportAxiomString, formulaMeaning_impString,
    formulaMeaning_equalityString, firstSuccessFamily, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hdiagonal : ∀ x z : M,
      (firstSuccessGraph y').val.Evalb ![x, z] ↔
        (eventualGraph y').val.Evalb ![x, z] := by
    have h := consequence_iff.mp
      (Theory.Proof.sound (firstSuccessGraph_uniform_eventualGraph y'))
      M inferInstance
    simpa [models_iff] using h
  have hsemantic :
      (∀ x z : M,
        (firstSuccessGraph y).val.Evalb ![x, z] ↔
          (eventualGraph y').val.Evalb ![x, z]) →
      (∀ x z : M,
        (firstSuccessGraph y).val.Evalb ![x, z] ↔
          (eventualGraph d).val.Evalb ![x, z]) →
      ∀ x z : M,
        (firstSuccessGraph y').val.Evalb ![x, z] ↔
          (eventualGraph d).val.Evalb ![x, z] := by
    intro he hp x z
    exact (hdiagonal x z).trans ((he x z).symm.trans (hp x z))
  simpa [models_iff] using hsemantic

/-! ## Soundness of the additive presentation -/

theorem transportRepairLogicalAxiom_meaning_provable
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (transportRepairTheoryPresentation w).syn.logicalAxiom.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  change transportRepairLogicalAxiomTest s = true at h
  rw [transportRepairLogicalAxiomTest_eq_true_iff] at h
  rcases h with hold | htransport
  · apply extendedLogicalAxiom_meaning_provable w
    exact (extendedLogicalAxiomTest_eq_true_iff s).mpr hold
  · rw [transportAxiomShape_iff] at htransport
    obtain ⟨y, y', d, rfl⟩ := htransport
    exact provable_PA_meaning_transportAxiom y y' d

theorem transportRepairTheoryAxiom_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {s : FormulaString}
    (h : (transportRepairTheoryPresentation w).ax.Holds s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  apply extendedTheoryAxiom_meaning_provable w hstage
  simpa [extendedTheoryPresentation, transportRepairTheoryPresentation] using h

private theorem transportRepair_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem transportRepairProofLines_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ i, i < Ψ.length →
      LineJustified (transportRepairTheoryPresentation w) Ψ i) :
    ∀ i, i < Ψ.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, hcase⟩ := hj i hi
    rcases hcase with hlog | hax | ⟨j, hji, k, hki, himp⟩
    · exact transportRepairLogicalAxiom_meaning_provable w hlog
    · exact transportRepairTheoryAxiom_meaning_provable w hstage hax
    · have hjlen : j < Ψ.length := Nat.lt_trans hji hi
      have hklen : k < Ψ.length := Nat.lt_trans hki hi
      have hAntecedent := ih j hji hjlen
      have hImplication := ih k hki hklen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem transportRepairIsProofList_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ψ : ProofSequence} {s : FormulaString}
    (hΨ : IsProofList (transportRepairTheoryPresentation w) Ψ s) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := transportRepairProofLines_meaning_provable w hstage hj
    (Ψ.length - 1) hidx
  rw [transportRepair_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem transportRepairProof_T_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (transportRepairTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  transportRepairIsProofList_meaning_sound w hstage hp

/-! ## Compatibility at the selected r.e.-theory endpoint -/

theorem transportRepairLogicalAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool) {s : FormulaString}
    (h : (transportRepairTheoryPresentation w).syn.logicalAxiom.Holds s) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily s :=
  WeakerThan.pbl (transportRepairLogicalAxiom_meaning_provable w h)

theorem transportRepairTheoryAxiom_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {s : FormulaString}
    (h : (transportRepairTheoryPresentation w).ax.Holds s) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  apply extendedTheoryAxiom_meaning_provable_in T w hstage
  simpa [extendedTheoryPresentation, transportRepairTheoryPresentation] using h

theorem transportRepairProofLines_meaning_provable_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence}
    (hj : ∀ i, i < Ψ.length →
      LineJustified (transportRepairTheoryPresentation w) Ψ i) :
    ∀ i, i < Ψ.length →
      T ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, -, hcase⟩ := hj i hi
    rcases hcase with hlog | hax | ⟨j, hji, k, hki, himp⟩
    · exact transportRepairLogicalAxiom_meaning_provable_in T w hlog
    · exact transportRepairTheoryAxiom_meaning_provable_in T w hstage hax
    · have hjlen : j < Ψ.length := Nat.lt_trans hji hi
      have hklen : k < Ψ.length := Nat.lt_trans hki hi
      have hAntecedent := ih j hji hjlen
      have hImplication := ih k hki hklen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem transportRepairIsProofList_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {Ψ : ProofSequence} {s : FormulaString}
    (hΨ : IsProofList (transportRepairTheoryPresentation w) Ψ s) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily s := by
  obtain ⟨hne, hlast, hj⟩ := hΨ
  have hidx : Ψ.length - 1 < Ψ.length := by
    have : 0 < Ψ.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := transportRepairProofLines_meaning_provable_in
    T w hstage hj (Ψ.length - 1) hidx
  rw [transportRepair_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem transportRepairProof_T_meaning_sound_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → T ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (transportRepairTheoryPresentation w) p a) :
    T ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  transportRepairIsProofList_meaning_sound_in T w hstage hp

/-- A repair proof of an equality tag has the intended meaning in every theory
that contains PA in provability strength. -/
theorem repairPrfEq_sound
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r : ℕ} (hp : RepairPrfEq T hRE p q r) :
    T ⊢ uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  have h := transportRepairProof_T_meaning_sound_in T
    (reTheoryStageWitness T hRE)
    (reTheoryStageWitness_sound T hRE) hp
  simpa [equalityCode, firstSuccessFamily, eventualFamily] using h

/-- Standard existential compatibility from the repair checker back to the
production checker at equality endpoints.  The target proof code is obtained
through theorem-stage existence, so this theorem is not an effective
backtranslation. -/
theorem repairPrfEq_to_exists_prfEq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {p q r : ℕ} (hp : RepairPrfEq T hRE p q r) :
    ∃ p' : ℕ, PrfEq T hRE p' q r := by
  apply (reTheory_provable_uniform_iff_exists_equalityCode_proof_T
    T hRE q r).mp
  exact repairPrfEq_sound T hRE hp

theorem exists_repairPrfEq_iff_exists_prfEq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) (q r : ℕ) :
    (∃ p : ℕ, RepairPrfEq T hRE p q r) ↔
      ∃ p : ℕ, PrfEq T hRE p q r := by
  constructor
  · rintro ⟨p, hp⟩
    exact repairPrfEq_to_exists_prfEq T hRE hp
  · rintro ⟨p, hp⟩
    exact ⟨p, prfEq_to_repairPrfEq T hRE hp⟩

/-- The remaining effective migration obligation.  No inhabitant is asserted:
an inhabitant would turn repair proof codes back into production proof codes
uniformly at all equality endpoints. -/
def HasPrimitiveRecursiveRepairBacktranslation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) : Prop :=
  ∃ back : ℕ → ℕ,
    Primrec back ∧
      ∀ p q r : ℕ,
        RepairPrfEq T hRE p q r → PrfEq T hRE (back p) q r

end FailureOfComposition.PrfEqTransportRepair
