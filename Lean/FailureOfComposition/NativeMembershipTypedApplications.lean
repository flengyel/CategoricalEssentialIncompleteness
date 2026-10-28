/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeMembershipApplications
import FailureOfComposition.ProofSearchMembership

/-!
# Typed native membership assembly

Coded-object membership and normalized representatives are fixed at theorem
level. Their chosen compiler dependencies remain outside the numerical and
general internal layers. No effective selection of these templates is claimed.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FailureOfComposition.NativeFamilyExtraction
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalAxiomGraph
open FailureOfComposition.CodedObjectMembership
open FailureOfComposition.ProofSearchMembership

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem exists_typed_membership_proof (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (Z : STObjectCode) (h k : ℕ) (e t m p u d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq (memberFormula Z)
        (typedRepresentative Z h) (typedRepresentative Z k)⌝ : V)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, t, (⌜totality (memberFormula Z) (typedRepresentative Z k)⌝ : V)])
    (hm : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, m, instanceValue (memberFormula Z).val ![u]])
    (hp : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, p, instanceValue (membershipFormula S (typedRepresentative Z h)).val ![u, d]]) :
    ∃ o : V, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, instanceValue (membershipFormula S (typedRepresentative Z k)).val ![u, d]] :=
  exists_membership_proof S (memberFormula Z) (typedRepresentative Z h)
    (typedRepresentative Z k) e t m p u d he ht hm hp

theorem exists_typed_transfer_closure_proof (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (Z : STObjectCode) (h k : ℕ) (e t d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq (memberFormula Z)
        (typedRepresentative Z h) (typedRepresentative Z k)⌝ : V)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, t, (⌜totality (memberFormula Z) (typedRepresentative Z k)⌝ : V)]) :
    ∃ o : V, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, instanceValue (transferClosure S (memberFormula Z)
        (typedRepresentative Z h) (typedRepresentative Z k)) ![d]] :=
  exists_transfer_closure_proof S (memberFormula Z) (typedRepresentative Z h)
    (typedRepresentative Z k) e t d he ht

end FailureOfComposition.NativeMembershipAssembly
