/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralComparisonPreservation
import FailureOfComposition.NativeNumeralProof

/-!
# Canonical acceptance of constructed comparison proofs

At the empty context, the eight seed premises are Foundation proofs. Each
constructor then gives a proof of its literal comparison target. The canonical
native checker accepts that actual output code. The signed constructors have
no comparison premise.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalAxiomGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

structure SeedProofs (S : ArithmeticTheory) [S.Δ₁]
    (r0 z1 refl as ltBridge nltBridge neForward neReverse : V) : Prop where
  r0_valid : Proof S r0 (⌜r0Sentence⌝ : V)
  z1_valid : Proof S z1 (⌜z1Sentence⌝ : V)
  refl_valid : Proof S refl (⌜reflSentence⌝ : V)
  as_valid : Proof S as (⌜asSentence⌝ : V)
  lt_valid : Proof S ltBridge (⌜ltBridgeSentence⌝ : V)
  nlt_valid : Proof S nltBridge (⌜nltBridgeSentence⌝ : V)
  forward_valid : Proof S neForward (⌜neForwardSentence⌝ : V)
  reverse_valid : Proof S neReverse (⌜neReverseSentence⌝ : V)

variable (S : ArithmeticTheory) [S.Δ₁]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse n m : V}

theorem SeedProofs.toSeedsIn
    (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse) :
    SeedsIn S 0 r0 z1 refl as ltBridge nltBridge neForward neReverse := by
  rcases hs with ⟨h0, h1, hr, ha, hl, hnl, hf, hv⟩
  constructor
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using h0
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using h1
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using hr
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using ha
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using hl
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using hnl
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using hf
  · simpa only [Proof, singleton_eq_insert, emptyset_def] using hv

theorem proof_eqValue (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse)
  (h : n = m) :
    Proof S (eqValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m) (eqTarget n m)
      := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_eqValue S (hs.toSeedsIn S) h

theorem eqValue_accepted (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : n = m) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, eqValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m, eqTarget n m] :=
  (accepted_iff_proof S _ _).mpr (proof_eqValue S hs h)

theorem eqGraph_preserves_acceptance {o : V}
    (ho : eqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, 0,
      n, m])
    (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : n = m) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, eqTarget n m] := by
  rw [(eqGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact eqValue_accepted S hs h

theorem proof_ltValue (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse)
  (h : n < m) :
    Proof S (ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m) (ltTarget n m)
      := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_ltValue S (hs.toSeedsIn S) h

theorem ltValue_accepted (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : n < m) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m, ltTarget n m] :=
  (accepted_iff_proof S _ _).mpr (proof_ltValue S hs h)

theorem ltGraph_preserves_acceptance {o : V}
    (ho : ltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, 0,
      n, m])
    (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : n < m) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, ltTarget n m] := by
  rw [(ltGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact ltValue_accepted S hs h

theorem proof_nltValue (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse)
  (h : m ≤ n) :
    Proof S (nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m) (nltTarget n
      m) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_nltValue S (hs.toSeedsIn S) h

theorem nltValue_accepted (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : m ≤ n) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m, nltTarget n m] :=
  (accepted_iff_proof S _ _).mpr (proof_nltValue S hs h)

theorem nltGraph_preserves_acceptance {o : V}
    (ho : nltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse,
      0, n, m])
    (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : m ≤ n) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, nltTarget n m] := by
  rw [(nltGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact nltValue_accepted S hs h

theorem proof_neValue (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse)
  (h : n ≠ m) :
    Proof S (neValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m) (neTarget n m)
      := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_neValue S (hs.toSeedsIn S) h

theorem neValue_accepted (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : n ≠ m) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, neValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m, neTarget n m] :=
  (accepted_iff_proof S _ _).mpr (proof_neValue S hs h)

theorem neGraph_preserves_acceptance {o : V}
    (ho : neGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, 0,
      n, m])
    (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : n ≠ m) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, neTarget n m] := by
  rw [(neGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact neValue_accepted S hs h

theorem proof_signedEqValue (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    Proof S (signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m)
      (signedEqTarget n m) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_signedEqValue S (hs.toSeedsIn S)

theorem signedEqValue_accepted (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m,
        signedEqTarget n m] :=
  (accepted_iff_proof S _ _).mpr (proof_signedEqValue S hs)

theorem signedEqGraph_preserves_acceptance {o : V}
    (ho : signedEqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, 0, n, m])
    (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, signedEqTarget n m] := by
  rw [(signedEqGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact signedEqValue_accepted S hs

theorem proof_signedLtValue (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    Proof S (signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m)
      (signedLtTarget n m) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_signedLtValue S (hs.toSeedsIn S)

theorem signedLtValue_accepted (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse 0 n m,
        signedLtTarget n m] :=
  (accepted_iff_proof S _ _).mpr (proof_signedLtValue S hs)

theorem signedLtGraph_preserves_acceptance {o : V}
    (ho : signedLtGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, 0, n, m])
    (hs : SeedProofs S r0 z1 refl as ltBridge nltBridge neForward neReverse) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, o, signedLtTarget n m] := by
  rw [(signedLtGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact signedLtValue_accepted S hs

end FailureOfComposition.NativeNumeralComparison
