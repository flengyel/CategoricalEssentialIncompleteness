/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeContextSpecialization

/-!
Audit-only declarations used to test the native-specialization dependency
guard.  This module is not imported by the mathematical library umbrella.
-/

@[expose] public section

set_option autoImplicit false

namespace FailureOfComposition.NativeContextSpecialization.AuditFixtures

private noncomputable def privateChoiceValue : Nat :=
  Classical.choice (show Nonempty Nat from ⟨37⟩)

/-- A noncomputable audit root whose body reaches a private choice-producing
helper. -/
noncomputable def noncomputableRoot : Nat :=
  privateChoiceValue

/-- The proof retains a classical witness; executable bodies must stop their
traversal at this theorem. -/
theorem theoremOnlyClassical : True :=
  (show ∃ n : Nat, n = n from
    ⟨Classical.choice (show Nonempty Nat from ⟨43⟩), rfl⟩).elim
      (fun _ _ => True.intro)

/-- The theorem is used only as the proof in a decidable branch. -/
def theoremOnlyClassicalRoot : Nat :=
  @ite Nat True (.isTrue theoremOnlyClassical) 41 0

end FailureOfComposition.NativeContextSpecialization.AuditFixtures
