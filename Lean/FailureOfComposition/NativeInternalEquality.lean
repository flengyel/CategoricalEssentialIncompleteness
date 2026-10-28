/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeInternalCorrectness
import FailureOfComposition.NativeInternalAxiomGraph
import FailureOfComposition.NativeInternalNat

/-!
# Internal recognition and transport of equality proofs

The equality-checking formula has coordinates `(proofCode,q,r)`.
It computes the literal equality formula code and applies the structural
proof checker.  All proof codes and indices in the preservation theorem
range over the ambient PA model.  A separate theorem fixes one standard
seed before quantifying over theories and models.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalEquality

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalCorrectness
open FailureOfComposition.NativeInternalAxiomGraph
open FailureOfComposition.NativeInternalNat
open FailureOfComposition.NativeEqualityTransport

/-- Coordinates `(proofCode,q,r)`.  The equality code is computed by its
existing exact internal graph. -/
noncomputable def nativeEqCheckFormula (A : 𝚺₁.Semisentence 2) :
    𝚺₁.Semisentence 3 := .mkSigma
  “p q r. ∃ a, !eqValueGraph a q r ∧ !(nativeProofCheckGraph A).val 1 p a”

theorem nativeEqCheckFormula_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    {S : ArithmeticTheory} [S.Δ₁] (hS : TheoryAxiomAgreement (V := V) A S)
    (p q r : V) :
    Semiformula.Evalb (M := V) ![p, q, r] (nativeEqCheckFormula A).val ↔
      Proof S p (eqValue q r) := by
  simp [nativeEqCheckFormula, eqValueGraph_iff, nativeProofCheckGraph_correct hA hS]

theorem nativeEqCheckFormula_nat_iff
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax) (p q r : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, q, r] (nativeEqCheckFormula A).val ↔
      FailureOfComposition.NativeProofChecker.nativeEqProofCheck ax p q r = true := by
  simp [nativeEqCheckFormula, eqValueGraph_nat_iff, nativeProofCheckGraph_nat_iff hA hnum,
    FailureOfComposition.NativeProofChecker.nativeEqProofCheck, boolBit]

/-- Acceptance preservation with an arbitrary supplied internal seed. -/
theorem transportGraph_preserves_acceptance
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    {S : ArithmeticTheory} [S.Δ₁] (hS : TheoryAxiomAgreement (V := V) A S)
    {y k e p q r c : V}
    (hy : Semiformula.Evalb (M := V) ![y, k, 0, e, p, q, r, c] transportGraph.val)
    (hk : Semiformula.Evalb (M := V) ![1, k, (⌜theta⌝ : V)] (nativeProofCheckGraph A).val)
    (he : Semiformula.Evalb (M := V) ![e, q, r] (nativeEqCheckFormula A).val)
    (hp : Semiformula.Evalb (M := V) ![p, q, c] (nativeEqCheckFormula A).val) :
    Semiformula.Evalb (M := V) ![y, r, c] (nativeEqCheckFormula A).val := by
  apply (nativeEqCheckFormula_iff hA hS y r c).mpr
  have hk' : Proof S k (⌜theta⌝ : V) := by
    simpa [nativeProofCheckGraph_correct hA hS] using hk
  have he' := (nativeEqCheckFormula_iff hA hS e q r).mp he
  have hp' := (nativeEqCheckFormula_iff hA hS p q c).mp hp
  rw [(transportGraph_iff y k 0 e p q r c).mp hy]
  simpa [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_transportValue S
      (by simpa [Proof, singleton_eq_insert, emptyset_def] using hk')
      (by simpa [Proof, singleton_eq_insert, emptyset_def] using he')
      (by simpa [Proof, singleton_eq_insert, emptyset_def] using hp')

/-- The witness precedes the theory, model, and all internal codes. -/
theorem exists_uniform_seed_acceptance :
    ∃ seed : ℕ, ∀ (S : ArithmeticTheory) [S.Δ₁]
      (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      Semiformula.Evalb (M := V) ![1, ORingStructure.numeral seed, (⌜theta⌝ : V)]
        (nativeProofCheckGraph (canonicalAxiomGraph S)).val ∧
      ∀ y e p q r c : V,
        Semiformula.Evalb (M := V)
          ![y, ORingStructure.numeral seed, 0, e, p, q, r, c] transportGraph.val →
        Semiformula.Evalb (M := V) ![e, q, r]
          (nativeEqCheckFormula (canonicalAxiomGraph S)).val →
        Semiformula.Evalb (M := V) ![p, q, c]
          (nativeEqCheckFormula (canonicalAxiomGraph S)).val →
        Semiformula.Evalb (M := V) ![y, r, c]
          (nativeEqCheckFormula (canonicalAxiomGraph S)).val := by
  rcases exists_uniform_theta_seed with ⟨seed, hseed⟩
  refine ⟨seed, ?_⟩
  intro S _ V _ _
  have hk : Semiformula.Evalb (M := V)
      ![1, ORingStructure.numeral seed, (⌜theta⌝ : V)]
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val := by
    rw [nativeProofCheckGraph_correct (canonicalAxiomGraph_computational S)
      (canonicalAxiomGraph_theory S)]
    exact Or.inl ⟨rfl, by
      simpa [Proof, singleton_eq_insert, emptyset_def] using hseed S V⟩
  refine ⟨hk, ?_⟩
  intro y e p q r c hy he hp
  exact transportGraph_preserves_acceptance
    (canonicalAxiomGraph_computational S) (canonicalAxiomGraph_theory S) hy hk he hp

end FailureOfComposition.NativeInternalEquality
