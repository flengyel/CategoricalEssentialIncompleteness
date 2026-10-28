/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralPreservation
import FailureOfComposition.NativeInternalCorrectness
import FailureOfComposition.NativeInternalAxiomGraph

/-!
# Native checker acceptance of numeral-arithmetic outputs

At the empty context, the derivation theorems give Foundation's `Proof`
predicate. The canonical native checker recognizes exactly that predicate.
The graph-based corollaries assume acceptance of the supplied seeds and
conclude acceptance of the exact constructed output, not just existence of
an arithmetical proof.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalCorrectness
open FailureOfComposition.NativeInternalAxiomGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem proof_addValue (S : ArithmeticTheory) [S.Δ₁] {r0 z1 refl as n m : V}
    (h0 : Proof S r0 (⌜r0Sentence⌝ : V)) (h1 : Proof S z1 (⌜z1Sentence⌝ : V))
    (hr : Proof S refl (⌜reflSentence⌝ : V)) (ha : Proof S as (⌜asSentence⌝ : V)) :
    Proof S (addValue r0 z1 refl as 0 n m) (addEq n m) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using derivationOf_addValue S
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using h0)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using h1)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hr)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using ha)

theorem proof_mulValue (S : ArithmeticTheory) [S.Δ₁] {r0 z1 refl as m0 m1 ms n m : V}
    (h0 : Proof S r0 (⌜r0Sentence⌝ : V)) (h1 : Proof S z1 (⌜z1Sentence⌝ : V))
    (hr : Proof S refl (⌜reflSentence⌝ : V)) (ha : Proof S as (⌜asSentence⌝ : V))
    (hm0 : Proof S m0 (⌜m0Sentence⌝ : V)) (hm1 : Proof S m1 (⌜m1Sentence⌝ : V))
    (hms : Proof S ms (⌜msSentence⌝ : V)) :
    Proof S (mulValue r0 z1 refl as m0 m1 ms 0 n m) (mulEq n m) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using derivationOf_mulValue S
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using h0)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using h1)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hr)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using ha)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hm0)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hm1)
    (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hms)

theorem accepted_iff_proof (S : ArithmeticTheory) [S.Δ₁] (d c : V) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, d, c] ↔ Proof S d c := by
  rw [nativeProofCheckGraph_correct (canonicalAxiomGraph_computational S)
    (canonicalAxiomGraph_theory S)]
  simp

theorem addGraph_preserves_acceptance (S : ArithmeticTheory) [S.Δ₁] {o r0 z1 refl as n m : V}
    (ho : addGraph.val.Evalb ![o, r0, z1, refl, as, 0, n, m])
    (h0 : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, r0, (⌜r0Sentence⌝ : V)])
    (h1 : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, z1, (⌜z1Sentence⌝ : V)])
    (hr : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, refl, (⌜reflSentence⌝ : V)])
    (ha : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, as, (⌜asSentence⌝ : V)]) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, addEq n m] := by
  apply (accepted_iff_proof S _ _).mpr
  rw [(addGraph_iff _ _ _ _ _ _ _ _).mp ho]
  exact proof_addValue S ((accepted_iff_proof S _ _).mp h0) ((accepted_iff_proof S _ _).mp h1)
    ((accepted_iff_proof S _ _).mp hr) ((accepted_iff_proof S _ _).mp ha)

theorem mulGraph_preserves_acceptance (S : ArithmeticTheory) [S.Δ₁]
    {o r0 z1 refl as m0 m1 ms n m : V}
    (ho : mulGraph.val.Evalb ![o, r0, z1, refl, as, m0, m1, ms, 0, n, m])
    (h0 : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, r0, (⌜r0Sentence⌝ : V)])
    (h1 : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, z1, (⌜z1Sentence⌝ : V)])
    (hr : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, refl, (⌜reflSentence⌝ : V)])
    (ha : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, as, (⌜asSentence⌝ : V)])
    (hm0 : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, m0, (⌜m0Sentence⌝ : V)])
    (hm1 : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, m1, (⌜m1Sentence⌝ : V)])
    (hms : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, ms, (⌜msSentence⌝ : V)]) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, mulEq n m] := by
  apply (accepted_iff_proof S _ _).mpr
  rw [(mulGraph_iff _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact proof_mulValue S ((accepted_iff_proof S _ _).mp h0) ((accepted_iff_proof S _ _).mp h1)
    ((accepted_iff_proof S _ _).mp hr) ((accepted_iff_proof S _ _).mp ha)
    ((accepted_iff_proof S _ _).mp hm0) ((accepted_iff_proof S _ _).mp hm1)
    ((accepted_iff_proof S _ _).mp hms)

end FailureOfComposition.NativeNumeralArithmetic
