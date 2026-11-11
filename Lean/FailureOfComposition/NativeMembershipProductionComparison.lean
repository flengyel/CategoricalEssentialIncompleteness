/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeMembershipTypedApplications

/-!
# Standard membership comparison with the production checker

After existentially quantifying proof codes, Craig-native and production
typed membership agree over natural numbers. This is neither an all-model
comparison nor a primitive-recursive translation of proof witnesses.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FailureOfComposition.NativeInternalApplications
open FailureOfComposition.CodedObjectMembership
open FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.ProofSearchMembership

theorem craig_typed_membership_nat_iff
    (T : ArithmeticTheory) [T.RE] [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h d u : ℕ) :
    (membershipFormula T.craig (typedRepresentative Z h)).val.Evalb ![u, d] ↔
      (typedProofSearchMembershipFormula T hRE Z h d).val.Evalb ![u] := by
  rw [membershipFormula_eval, typedProofSearchMembershipFormula_nat_iff]
  apply exists_congr
  intro y
  apply and_congr Iff.rfl
  exact (craig_eq_acceptance_iff_eqIndex T y d).trans
    ((classOf_eq_classOf_iff T y d).symm.trans
      (classOf_eq_classOf_iff_exists_prfEq T hRE y d))

end FailureOfComposition.NativeMembershipAssembly
