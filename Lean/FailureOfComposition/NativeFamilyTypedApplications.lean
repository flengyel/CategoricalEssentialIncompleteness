/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeFamilyApplications
import FailureOfComposition.ProofSearchMembership

/-!
# Typed application of native family extraction

Coded-object membership and representative normalization are fixed external
parameters here. Their choices do not enter the executable numerical core.
This separate import boundary also keeps typed model instances out of the
general extraction layer.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalAxiomGraph
open FailureOfComposition.NativeInternalEquality
open FailureOfComposition.CodedObjectMembership
open FailureOfComposition.ProofSearchMembership

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem exists_typed_family_transport
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (Z : STObjectCode) (h k : ℕ) (e u y r p d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq (memberFormula Z)
        (typedRepresentative Z h) (typedRepresentative Z k)⌝ : V)])
    (hm : (memberFormula Z).val.Evalb ![u])
    (hh : (outputGraph (typedRepresentative Z h)).val.Evalb ![u, y])
    (hk : (outputGraph (typedRepresentative Z k)).val.Evalb ![u, r])
    (hp : (nativeEqCheckFormula (canonicalAxiomGraph S)).val.Evalb ![p, y, d]) :
    ∃ q : V, (nativeEqCheckFormula (canonicalAxiomGraph S)).val.Evalb ![q, r, d] :=
  exists_family_transport S (memberFormula Z) (typedRepresentative Z h)
    (typedRepresentative Z k) e u y r p d he hm hh hk hp

end FailureOfComposition.NativeFamilyExtraction
