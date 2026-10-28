/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralComparisonProof

/-!
# Fixed standard comparison seeds

Fix a delta-one theory extending PA-minus. One tuple of eight standard proof
codes is chosen before the PA model and its numeral values. Embedding those
codes gives accepted internal outputs of the two explicit signed functions.
The executable functions use only the fixed codes and the numerical inputs.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

open FFL.Entailment
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalAxiomGraph

universe u

def StandardSeeds (S : ArithmeticTheory) [S.Δ₁] (s : Seeds8 ℕ) : Prop :=
  ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
    SeedProofs S (ORingStructure.numeral s.1.1.1 : V) (ORingStructure.numeral s.1.1.2 : V)
      (ORingStructure.numeral s.1.2.1 : V) (ORingStructure.numeral s.1.2.2 : V)
      (ORingStructure.numeral s.2.1.1 : V) (ORingStructure.numeral s.2.1.2 : V)
      (ORingStructure.numeral s.2.2.1 : V) (ORingStructure.numeral s.2.2.2 : V)

private theorem exists_standard_seed (S : ArithmeticTheory) [S.Δ₁]
    (phi : ArithmeticSentence) (hp : S ⊢ phi) :
    ∃ seed : ℕ, ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      Proof S (ORingStructure.numeral seed : V) (⌜phi⌝ : V) := by
  let d : S ⊢! phi := hp.get
  refine ⟨(⌜d⌝ : ℕ), ?_⟩
  intro V _ _
  rw [numeral_eq_natCast_app, coe_quote_proof_eq]
  exact proof_of_quote_proof d

theorem exists_standard_seeds (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S] :
    ∃ s : Seeds8 ℕ, StandardSeeds.{u} S s := by
  obtain ⟨s0, h0⟩ := exists_standard_seed S _ (WeakerThan.pbl r0_provable)
  obtain ⟨s1, h1⟩ := exists_standard_seed S _ (WeakerThan.pbl z1_provable)
  obtain ⟨s2, h2⟩ := exists_standard_seed S _ (WeakerThan.pbl refl_provable)
  obtain ⟨s3, h3⟩ := exists_standard_seed S _ (WeakerThan.pbl as_provable)
  obtain ⟨s4, h4⟩ := exists_standard_seed S _ (WeakerThan.pbl ltBridge_provable)
  obtain ⟨s5, h5⟩ := exists_standard_seed S _ (WeakerThan.pbl nltBridge_provable)
  obtain ⟨s6, h6⟩ := exists_standard_seed S _ (WeakerThan.pbl neForward_provable)
  obtain ⟨s7, h7⟩ := exists_standard_seed S _ (WeakerThan.pbl neReverse_provable)
  refine ⟨(((s0, s1), (s2, s3)), ((s4, s5), (s6, s7))), ?_⟩
  intro V _ _
  exact ⟨h0 V, h1 V, h2 V, h3 V, h4 V, h5 V, h6 V, h7 V⟩

def signedEqWithSeeds (s : Seeds8 ℕ) (nm : ℕ × ℕ) : ℕ :=
  signedEqCode s.1.1.1 s.1.1.2 s.1.2.1 s.1.2.2 s.2.1.1 s.2.1.2 s.2.2.1 s.2.2.2 0 nm.1 nm.2

theorem primrec_signedEqWithSeeds (s : Seeds8 ℕ) : Primrec (signedEqWithSeeds s) :=
  primrec_signedEqCode (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec.const 0) Primrec.fst Primrec.snd

def signedLtWithSeeds (s : Seeds8 ℕ) (nm : ℕ × ℕ) : ℕ :=
  signedLtCode s.1.1.1 s.1.1.2 s.1.2.1 s.1.2.2 s.2.1.1 s.2.1.2 s.2.2.1 s.2.2.2 0 nm.1 nm.2

theorem primrec_signedLtWithSeeds (s : Seeds8 ℕ) : Primrec (signedLtWithSeeds s) :=
  primrec_signedLtCode (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec.const 0) Primrec.fst Primrec.snd

section Internal

variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def signedEqSeedValue (s : Seeds8 ℕ) (n m : V) : V :=
  signedEqValue (ORingStructure.numeral s.1.1.1 : V) (ORingStructure.numeral s.1.1.2 : V)
    (ORingStructure.numeral s.1.2.1 : V) (ORingStructure.numeral s.1.2.2 : V)
    (ORingStructure.numeral s.2.1.1 : V) (ORingStructure.numeral s.2.1.2 : V)
    (ORingStructure.numeral s.2.2.1 : V) (ORingStructure.numeral s.2.2.2 : V) 0 n m

noncomputable def signedLtSeedValue (s : Seeds8 ℕ) (n m : V) : V :=
  signedLtValue (ORingStructure.numeral s.1.1.1 : V) (ORingStructure.numeral s.1.1.2 : V)
    (ORingStructure.numeral s.1.2.1 : V) (ORingStructure.numeral s.1.2.2 : V)
    (ORingStructure.numeral s.2.1.1 : V) (ORingStructure.numeral s.2.1.2 : V)
    (ORingStructure.numeral s.2.2.1 : V) (ORingStructure.numeral s.2.2.2 : V) 0 n m

theorem standard_comparison_endpoint (S : ArithmeticTheory) [S.Δ₁]
    (s : Seeds8 ℕ) (hs : StandardSeeds.{u} S s) (n m : V) :
    signedEqGraph.val.Evalb ![signedEqSeedValue s n m, (ORingStructure.numeral s.1.1.1 : V),
      (ORingStructure.numeral s.1.1.2 : V), (ORingStructure.numeral s.1.2.1 : V),
      (ORingStructure.numeral s.1.2.2 : V), (ORingStructure.numeral s.2.1.1 : V),
      (ORingStructure.numeral s.2.1.2 : V), (ORingStructure.numeral s.2.2.1 : V),
      (ORingStructure.numeral s.2.2.2 : V), 0, n, m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedEqSeedValue s n m, signedEqTarget n m] ∧
    signedLtGraph.val.Evalb ![signedLtSeedValue s n m, (ORingStructure.numeral s.1.1.1 : V),
      (ORingStructure.numeral s.1.1.2 : V), (ORingStructure.numeral s.1.2.1 : V),
      (ORingStructure.numeral s.1.2.2 : V), (ORingStructure.numeral s.2.1.1 : V),
      (ORingStructure.numeral s.2.1.2 : V), (ORingStructure.numeral s.2.2.1 : V),
      (ORingStructure.numeral s.2.2.2 : V), 0, n, m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedLtSeedValue s n m, signedLtTarget n m] := by
  refine ⟨(signedEqGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr rfl, ?_,
    (signedLtGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr rfl, ?_⟩
  · exact signedEqValue_accepted S (hs V)
  · exact signedLtValue_accepted S (hs V)

end Internal

theorem signedEqSeedValue_nat (s : Seeds8 ℕ) (n m : ℕ) :
    signedEqSeedValue s n m = signedEqWithSeeds s (n, m) := by
  simp only [signedEqSeedValue, signedEqWithSeeds, numeral_eq_natCast_app,
    natCast_nat, signedEqValue_nat]

theorem signedLtSeedValue_nat (s : Seeds8 ℕ) (n m : ℕ) :
    signedLtSeedValue s n m = signedLtWithSeeds s (n, m) := by
  simp only [signedLtSeedValue, signedLtWithSeeds, numeral_eq_natCast_app,
    natCast_nat, signedLtValue_nat]

theorem comparison_functions_nat_accepted (S : ArithmeticTheory) [S.Δ₁]
    (s : Seeds8 ℕ) (hs : StandardSeeds.{0} S s) (n m : ℕ) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedEqWithSeeds s (n, m), signedEqTargetCode n m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedLtWithSeeds s (n, m), signedLtTargetCode n m] := by
  have h := standard_comparison_endpoint (V := ℕ) S s hs n m
  have he := h.2.1
  have hl := h.2.2.2
  rw [signedEqSeedValue_nat, signedEqTarget_nat] at he
  rw [signedLtSeedValue_nat, signedLtTarget_nat] at hl
  exact ⟨he, hl⟩

theorem exists_standard_comparison_functions (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S] :
    ∃ s : Seeds8 ℕ, StandardSeeds.{u} S s ∧
      Primrec (signedEqWithSeeds s) ∧ Primrec (signedLtWithSeeds s) ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔], ∀ n m : V,
    signedEqGraph.val.Evalb ![signedEqSeedValue s n m, (ORingStructure.numeral s.1.1.1 : V),
      (ORingStructure.numeral s.1.1.2 : V), (ORingStructure.numeral s.1.2.1 : V),
      (ORingStructure.numeral s.1.2.2 : V), (ORingStructure.numeral s.2.1.1 : V),
      (ORingStructure.numeral s.2.1.2 : V), (ORingStructure.numeral s.2.2.1 : V),
      (ORingStructure.numeral s.2.2.2 : V), 0, n, m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedEqSeedValue s n m, signedEqTarget n m] ∧
    signedLtGraph.val.Evalb ![signedLtSeedValue s n m, (ORingStructure.numeral s.1.1.1 : V),
      (ORingStructure.numeral s.1.1.2 : V), (ORingStructure.numeral s.1.2.1 : V),
      (ORingStructure.numeral s.1.2.2 : V), (ORingStructure.numeral s.2.1.1 : V),
      (ORingStructure.numeral s.2.1.2 : V), (ORingStructure.numeral s.2.2.1 : V),
      (ORingStructure.numeral s.2.2.2 : V), 0, n, m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedLtSeedValue s n m, signedLtTarget n m] := by
  obtain ⟨s, hs⟩ := exists_standard_seeds S
  refine ⟨s, hs, primrec_signedEqWithSeeds s, primrec_signedLtWithSeeds s, ?_⟩
  intro V _ _ n m
  exact standard_comparison_endpoint S s hs n m

end FailureOfComposition.NativeNumeralComparison
