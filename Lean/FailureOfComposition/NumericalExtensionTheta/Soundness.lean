/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionTheta.Core
import FailureOfComposition.NumericalExtensionComposition.Soundness
import FailureOfComposition.ConcreteAdequacy

/-!
# Graph semantics and PA meaning of the B1(8) theta scheme

The graph theorem is uniform in all internal inputs and outputs of an
arbitrary PA model, while `q` remains a fixed external program index.  The
subsequent proof-code scheme concerns fixed external natural numbers.  These
two levels are kept separate.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalExtensionTheta

open ConcreteEvaluator FiniteExtensionChecker NumericalExtensionComposition
open NumericalExtensionProofs NumericalProofBridge ProofSearch
open TypedNearProduct UniformIndexQuotient

noncomputable section

/-! ## The all-internal graph law -/

set_option maxHeartbeats 1000000 in
-- Expanding the two compositions, tensor, checker, and projection is costly.
/-- For fixed external `q`, the theta program succeeds on an internally coded
pair `(t,i)` exactly when `q(t)=c` for some internal `c` and the canonical
internal formula `Ext(c,i)` holds. -/
@[simp] theorem eventualGraph_thetaIndex_pair_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (t i y : M) :
    (eventualGraph (thetaIndex q)).val.Evalb ![pair t i, y] ↔
      y = i ∧ ∃ c : M,
        (eventualGraph q).val.Evalb ![t, c] ∧
          extensionFormula.val.Evalb ![c, i] := by
  rw [thetaIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, hinner, hprojection⟩
    rw [eventualGraph_comp_eval] at hinner
    obtain ⟨u, htensor, hchecker⟩ := hinner
    rw [eventualGraph_tensorIndex_eval] at htensor
    simp only [pi₁_pair, pi₂_pair] at htensor
    obtain ⟨c, j, hq, hj, rfl⟩ := htensor
    have hji : j = i :=
      (eventualGraph_identityIndex_eval i j).mp hj
    subst j
    obtain ⟨hz, hext⟩ :=
      (eventualGraph_extensionCheckerIndex_pair_eval c i z).mp hchecker
    subst z
    have hy : y = i := by
      simpa only [pi₂_pair] using
        (eventualGraph_secondProjectionIndex_eval (pair c i) y).mp
          hprojection
    exact ⟨hy, c, hq, hext⟩
  · rintro ⟨hy, c, hq, hext⟩
    subst y
    refine ⟨pair c i, ?_, ?_⟩
    · rw [eventualGraph_comp_eval]
      refine ⟨pair c i, ?_, ?_⟩
      · rw [eventualGraph_tensorIndex_pair_eval]
        exact ⟨hq, (eventualGraph_identityIndex_eval i i).mpr rfl⟩
      · exact (eventualGraph_extensionCheckerIndex_pair_eval c i
          (pair c i)).mpr ⟨rfl, hext⟩
    · exact (eventualGraph_secondProjectionIndex_eval
        (pair c i) i).mpr (by simp)

/-! ## Fixed-standard consequences -/

/-- Standard-model adequacy turns the graph equation into an actual
computation theorem for the production numbering. -/
theorem thetaIndex_computes_of_component_and_extension
    (q t c i : ℕ) (hq : c ∈ Kleene.eval q t)
    (hext : extensionFormula.val.Evalb ![c, i]) :
    i ∈ Kleene.eval (thetaIndex q) (Nat.pair t i) := by
  apply (eventualGraph_adequate (thetaIndex q) (Nat.pair t i) i).mp
  simpa only [nat_pair_eq] using
    (eventualGraph_thetaIndex_pair_eval (M := ℕ) q t i i).mpr
      ⟨rfl, c, (eventualGraph_adequate q t c).mpr hq, hext⟩

/-- PA proves the precise meaning of the new fixed-standard scheme. -/
theorem provable_PA_meaning_componentAndCheckerToTheta
    (q t c i : ℕ) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (componentAndCheckerToThetaAxiomString q t c i) := by
  simp only [componentAndCheckerToThetaAxiomString,
    formulaMeaning_impString, checkerInstanceString, thetaInstanceString,
    formulaMeaning_rightInstanceString, eventualFamily]
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have htc : (ORingStructure.numeral (Nat.pair t i) : M) =
      pair (ORingStructure.numeral t) (ORingStructure.numeral i) := by
    simpa only [numeral_eq_natCast] using
      (coe_pair_eq_pair_coe (V := M) t i)
  have hci : (ORingStructure.numeral (Nat.pair c i) : M) =
      pair (ORingStructure.numeral c) (ORingStructure.numeral i) := by
    simpa only [numeral_eq_natCast] using
      (coe_pair_eq_pair_coe (V := M) c i)
  have hsemantic :
      (eventualGraph q).val.Evalb
          ![(ORingStructure.numeral t : M),
            (ORingStructure.numeral c : M)] →
      (eventualGraph extensionCheckerIndex).val.Evalb
          ![(ORingStructure.numeral (Nat.pair c i) : M),
            (ORingStructure.numeral (Nat.pair c i) : M)] →
      (eventualGraph (thetaIndex q)).val.Evalb
          ![(ORingStructure.numeral (Nat.pair t i) : M),
            (ORingStructure.numeral i : M)] := by
    intro hq hchecker
    rw [hci, eventualGraph_extensionCheckerIndex_pair_eval] at hchecker
    rw [htc, eventualGraph_thetaIndex_pair_eval]
    exact ⟨rfl, ORingStructure.numeral c, hq, hchecker.2⟩
  simpa [models_iff, Semiformula.eval_substs,
    numeral_eq_natCast] using hsemantic

/-- Explicit PA instance of B1(8): the two supplied PA derivations imply the
theta computation derivation. -/
theorem PA_proves_theta_of_component_and_checker
    (q t c i : ℕ)
    (hq : 𝗣𝗔 ⊢ (eventualGraph q).val/[t, c])
    (hchecker : 𝗣𝗔 ⊢ (eventualGraph extensionCheckerIndex).val/[Nat.pair c i,
        Nat.pair c i]) :
    𝗣𝗔 ⊢ (eventualGraph (thetaIndex q)).val/[Nat.pair t i, i] := by
  have hscheme :=
    provable_PA_meaning_componentAndCheckerToTheta q t c i
  simp only [componentAndCheckerToThetaAxiomString,
    formulaMeaning_impString, checkerInstanceString, thetaInstanceString,
    formulaMeaning_rightInstanceString, eventualFamily] at hscheme
  exact Entailment.mdp (Entailment.mdp hscheme hq) hchecker

/-- Equivalent PA form with the canonical closed `Ext(c,i)` instance as the
second premise. -/
theorem PA_proves_theta_of_component_and_extension
    (q t c i : ℕ)
    (hq : 𝗣𝗔 ⊢ (eventualGraph q).val/[t, c])
    (hext : 𝗣𝗔 ⊢ extensionFormula.val/[c, i]) :
    𝗣𝗔 ⊢ (eventualGraph (thetaIndex q)).val/[Nat.pair t i, i] :=
  PA_proves_theta_of_component_and_checker q t c i hq
    ((proves_checker_iff_extension 𝗣𝗔 c i).mpr hext)

/-! ## Meaning soundness of the common checker -/

theorem extensionThetaLogicalAxiom_meaning_provable
    (w : ℕ → ℕ → Bool) {x : FormulaString}
    (h : (extensionThetaTheoryPresentation w).syn.logicalAxiom.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  change extensionThetaLogicalAxiomTest x = true at h
  rw [extensionThetaLogicalAxiomTest_eq_true_iff] at h
  rcases h with hcomposition | htheta
  · apply extensionCompositionLogicalAxiom_meaning_provable w
    exact (extensionCompositionLogicalAxiomTest_eq_true_iff x).mpr
      hcomposition
  · rw [extensionThetaAxiomShape_iff] at htheta
    obtain ⟨q, t, c, i, rfl⟩ := htheta
    exact provable_PA_meaning_componentAndCheckerToTheta q t c i

theorem extensionThetaTheoryAxiom_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {x : FormulaString}
    (h : (extensionThetaTheoryPresentation w).ax.Holds x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  apply extensionCompositionTheoryAxiom_meaning_provable w hstage
  simpa [extensionCompositionTheoryPresentation,
    extensionThetaTheoryPresentation] using h

private theorem extensionTheta_getD_last_eq (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

theorem extensionThetaProofLines_meaning_provable
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ps : ProofSequence}
    (hj : ∀ j, j < Ps.length →
      LineJustified (extensionThetaTheoryPresentation w) Ps j) :
    ∀ j, j < Ps.length →
      𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
        (Ps.getD j []) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlt
    obtain ⟨-, -, hcase⟩ := hj j hjlt
    rcases hcase with hlog | hax | ⟨u, huj, v, hvj, himp⟩
    · exact extensionThetaLogicalAxiom_meaning_provable w hlog
    · exact extensionThetaTheoryAxiom_meaning_provable w hstage hax
    · have hulen : u < Ps.length := Nat.lt_trans huj hjlt
      have hvlen : v < Ps.length := Nat.lt_trans hvj hjlt
      have hAntecedent := ih u huj hulen
      have hImplication := ih v hvj hvlen
      rw [himp, formulaMeaning_impString] at hImplication
      exact Entailment.mdp hImplication hAntecedent

theorem extensionThetaIsProofList_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {Ps : ProofSequence} {x : FormulaString}
    (hPs : IsProofList (extensionThetaTheoryPresentation w) Ps x) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily x := by
  obtain ⟨hne, hlast, hj⟩ := hPs
  have hidx : Ps.length - 1 < Ps.length := by
    have : 0 < Ps.length := List.length_pos_of_ne_nil hne
    omega
  have hlastLine := extensionThetaProofLines_meaning_provable
    w hstage hj (Ps.length - 1) hidx
  rw [extensionTheta_getD_last_eq, hlast] at hlastLine
  exact hlastLine

theorem extensionThetaProof_T_meaning_sound
    (w : ℕ → ℕ → Bool)
    (hstage : ∀ a k : ℕ, w a k = true → 𝗣𝗔 ⊢ decodedSentence a)
    {p a : ℕ}
    (hp : Proof_T (extensionThetaTheoryPresentation w) p a) :
    𝗣𝗔 ⊢ formulaMeaning firstSuccessFamily eventualFamily
      (decodeFormula a) :=
  extensionThetaIsProofList_meaning_sound w hstage hp

end

end FailureOfComposition.NumericalExtensionTheta
