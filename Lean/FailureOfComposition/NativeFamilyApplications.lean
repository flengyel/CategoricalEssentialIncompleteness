/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeFamilyPreservation
import FailureOfComposition.NativeFamilySeed
import FailureOfComposition.NativeFamilyNat
import FailureOfComposition.NativeFamilyPR
import FailureOfComposition.NativeFamilyNumeralInstances

/-!
# Native extraction and equality transport from family equality

True internal membership and computation instances supply proof witnesses by
formalized Sigma-one completeness. The numerical constructor then combines
them with the supplied family proof. No S-proof is interpreted as model truth,
and no selector for the completeness witnesses is asserted.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalCorrectness
open FailureOfComposition.NativeInternalAxiomGraph
open FailureOfComposition.NativeInternalEquality
open FailureOfComposition.NativeEqualityTransport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem extractGraph_preserves_acceptance
    (S : ArithmeticTheory) [S.Δ₁]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (hS : TheoryAxiomAgreement (V := V) A S)
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {o seed e m pH pK u y r : V}
    (ho : (extractGraph (extractionBodyCode M h k)).val.Evalb
      ![o, seed, 0, e, m, pH, pK, u, y, r])
    (hs : (nativeProofCheckGraph A).val.Evalb ![1, seed, (⌜extractionSeed M h k⌝ : V)])
    (he : (nativeProofCheckGraph A).val.Evalb ![1, e, (⌜familyEq M h k⌝ : V)])
    (hm : (nativeProofCheckGraph A).val.Evalb ![1, m, instanceValue M.val ![u]])
    (hh : (nativeProofCheckGraph A).val.Evalb ![1, pH, instanceValue (outputGraph h).val ![u, y]])
    (hk : (nativeProofCheckGraph A).val.Evalb ![1, pK, instanceValue (outputGraph k).val ![u, r]]) :
    (nativeEqCheckFormula A).val.Evalb ![o, y, r] := by
  apply (nativeEqCheckFormula_iff hA hS o y r).mpr
  have convertProof (p a : V) (hp : (nativeProofCheckGraph A).val.Evalb ![1, p, a]) :
      DerivationOf S p (insert a 0) := by
    simpa [nativeProofCheckGraph_correct hA hS, Proof, singleton_eq_insert, emptyset_def] using hp
  simpa [Proof, singleton_eq_insert, emptyset_def] using
    extractGraph_preserves_derivationOf S M h k ho
      (convertProof _ _ hs) (convertProof _ _ he) (convertProof _ _ hm)
      (convertProof _ _ hh) (convertProof _ _ hk)

/-- The seed is fixed after the theory and templates, before the model. -/
theorem exists_extraction_endpoint
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ∃ seed : ℕ, ∀ (W : Type*) [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗣𝗔]
      (e u y r : W),
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, e, (⌜familyEq M h k⌝ : W)] →
      M.val.Evalb ![u] → (outputGraph h).val.Evalb ![u, y] →
      (outputGraph k).val.Evalb ![u, r] →
      ∃ m pH pK o : W,
        (extractGraph (extractionBodyCode M h k)).val.Evalb
          ![o, ORingStructure.numeral seed, 0, e, m, pH, pK, u, y, r] ∧
        (nativeEqCheckFormula (canonicalAxiomGraph S)).val.Evalb ![o, y, r] := by
  obtain ⟨seed, hseed⟩ := exists_standard_extraction_seed S M h k
  refine ⟨seed, ?_⟩
  intro W _ _ e u y r he hm hh hk
  have : 𝗣𝗔⁻ ⪯ S := WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗣𝗔) inferInstance
  obtain ⟨m, hm⟩ := exists_canonical_sigma_instance S M ![u] hm
  obtain ⟨pH, hh⟩ := exists_canonical_sigma_instance S (outputGraph h) ![u, y] hh
  obtain ⟨pK, hk⟩ := exists_canonical_sigma_instance S (outputGraph k) ![u, r] hk
  obtain ⟨o, ho⟩ := extractGraph_total (extractionBodyCode M h k)
    (ORingStructure.numeral seed : W) 0 e m pH pK u y r
  exact ⟨m, pH, pK, o, ho, extractGraph_preserves_acceptance S
    (canonicalAxiomGraph_computational S) (canonicalAxiomGraph_theory S)
    M h k ho (hseed W) he hm hh hk⟩

theorem exists_output_equality
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u y r : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, e, (⌜familyEq M h k⌝ : V)])
    (hm : M.val.Evalb ![u]) (hh : (outputGraph h).val.Evalb ![u, y])
    (hk : (outputGraph k).val.Evalb ![u, r]) :
    ∃ o : V, (nativeEqCheckFormula (canonicalAxiomGraph S)).val.Evalb ![o, y, r] := by
  obtain ⟨_, hend⟩ := exists_extraction_endpoint S M h k
  obtain ⟨m, pH, pK, o, _, ho⟩ := hend V e u y r he hm hh hk
  exact ⟨o, ho⟩

/-- This composition uses the newly extracted output-equality proof. -/
theorem exists_family_transport
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u y r p d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, e, (⌜familyEq M h k⌝ : V)])
    (hm : M.val.Evalb ![u]) (hh : (outputGraph h).val.Evalb ![u, y])
    (hk : (outputGraph k).val.Evalb ![u, r])
    (hp : (nativeEqCheckFormula (canonicalAxiomGraph S)).val.Evalb ![p, y, d]) :
    ∃ q : V, (nativeEqCheckFormula (canonicalAxiomGraph S)).val.Evalb ![q, r, d] := by
  obtain ⟨o, ho⟩ := exists_output_equality S M h k e u y r he hm hh hk
  obtain ⟨seed, hseed⟩ := exists_uniform_seed_acceptance
  have hs := hseed S V
  obtain ⟨q, hq⟩ := transportGraph_total (ORingStructure.numeral seed : V) 0 o p y r d
  exact ⟨q, hs.2 q o p y r d hq ho hp⟩

theorem exists_craig_family_transport
    (T : ArithmeticTheory) [T.RE] [𝗣𝗔 ⪯ T]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u y r p d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : V)])
    (hm : M.val.Evalb ![u]) (hh : (outputGraph h).val.Evalb ![u, y])
    (hk : (outputGraph k).val.Evalb ![u, r])
    (hp : (nativeEqCheckFormula (canonicalAxiomGraph T.craig)).val.Evalb ![p, y, d]) :
    ∃ q : V, (nativeEqCheckFormula (canonicalAxiomGraph T.craig)).val.Evalb ![q, r, d] := by
  have : 𝗣𝗔 ⪯ T.craig := WeakerThan.trans (inferInstance : 𝗣𝗔 ⪯ T)
    (inferInstance : T ⪯ T.craig)
  exact exists_family_transport T.craig M h k e u y r p d he hm hh hk hp

end FailureOfComposition.NativeFamilyExtraction
