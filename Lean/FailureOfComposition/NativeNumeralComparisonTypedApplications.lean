/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralComparisonApplications
import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1

/-!
# Typed and Craig comparison applications

The standard-model adequacy interface converts acceptance of the constructed
codes into typed derivability of the signed numeral sentences. For an
r.e. theory extending PA-minus, the construction runs in its delta-one Craig
companion. Craig equivalence gives typed derivability in the original theory.
It does not identify proof codes of the two presentations.
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

def signedEqSentence (n m : ℕ) : ArithmeticSentence :=
  if n = m then “↑n = ↑m” else “↑n ≠ ↑m”

def signedLtSentence (n m : ℕ) : ArithmeticSentence :=
  if n < m then “↑n < ↑m” else “¬(↑n < ↑m)”

theorem signedEqSentence_encode (n m : ℕ) :
    encode (signedEqSentence n m) = signedEqTargetCode n m := by
  by_cases h : n = m <;>
    simp [signedEqSentence, signedEqTargetCode, h, eqTargetCode_encode, neTargetCode_encode]

theorem signedLtSentence_encode (n m : ℕ) :
    encode (signedLtSentence n m) = signedLtTargetCode n m := by
  by_cases h : n < m <;>
    simp [signedLtSentence, signedLtTargetCode, h, ltTargetCode_encode, nltTargetCode_encode]

theorem typed_signed_comparisons (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S] (n m : ℕ) :
    S ⊢ signedEqSentence n m ∧ S ⊢ signedLtSentence n m := by
  obtain ⟨s, hs⟩ := exists_standard_seeds.{0} S
  have h := comparison_functions_nat_accepted S s hs n m
  constructor
  · apply Provable.sound
    refine ⟨signedEqWithSeeds s (n, m), ?_⟩
    rw [Sentence.quote_eq_encode_nat, signedEqSentence_encode]
    exact (accepted_iff_proof S _ _).mp h.1
  · apply Provable.sound
    refine ⟨signedLtWithSeeds s (n, m), ?_⟩
    rw [Sentence.quote_eq_encode_nat, signedLtSentence_encode]
    exact (accepted_iff_proof S _ _).mp h.2

theorem craig_signedEq_adequacy (T : ArithmeticTheory) [T.RE] (n m : ℕ) :
    (∃ p : ℕ, (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, p, signedEqTargetCode n m]) ↔ T ⊢ signedEqSentence n m := by
  simp only [accepted_iff_proof]
  change Provable T.craig (signedEqTargetCode n m) ↔ T ⊢ signedEqSentence n m
  rw [← signedEqSentence_encode, ← Sentence.quote_eq_encode_nat]
  exact FailureOfComposition.NativeContextMP.craig_provable_iff T (signedEqSentence n m)

theorem craig_signedLt_adequacy (T : ArithmeticTheory) [T.RE] (n m : ℕ) :
    (∃ p : ℕ, (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, p, signedLtTargetCode n m]) ↔ T ⊢ signedLtSentence n m := by
  simp only [accepted_iff_proof]
  change Provable T.craig (signedLtTargetCode n m) ↔ T ⊢ signedLtSentence n m
  rw [← signedLtSentence_encode, ← Sentence.quote_eq_encode_nat]
  exact FailureOfComposition.NativeContextMP.craig_provable_iff T (signedLtSentence n m)

theorem craig_signed_comparisons (T : ArithmeticTheory) [T.RE] [𝗣𝗔⁻ ⪯ T] (n m : ℕ) :
    T ⊢ signedEqSentence n m ∧ T ⊢ signedLtSentence n m := by
  let : 𝗣𝗔⁻ ⪯ T.craig := WeakerThan.trans
    (inferInstance : 𝗣𝗔⁻ ⪯ T) (inferInstance : T ⪯ T.craig)
  have h := typed_signed_comparisons T.craig n m
  exact ⟨WeakerThan.pbl h.1, WeakerThan.pbl h.2⟩

end FailureOfComposition.NativeNumeralComparison
