/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedSoundness
public import CategoricalEssentialIncompleteness.V46MillerTheoryDomainApplication

/-! # Native consistency of the concrete T_a in the categorical application

The two finite-support proofs are interpreted in the constructed real model
with the same assignment. Consistency has the printed sentence-only scope;
the real-model proof is used for the actual base theory T_a.
-/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedConsistency

/-- The actual real model of T_a rules out a finite proof of a sentence and
an independently supported finite proof of its negation. -/
theorem theoryAxioms_consistent (a : Point) :
    TheoryDomainApplication.Consistent (RealClosedAxioms.theoryAxioms a) := by
  intro φ _ h
  have hp := RealClosedSoundness.finiteProof_real_sound a h.1 (fun _ => 0)
  have hn := RealClosedSoundness.finiteProof_real_sound a h.2 (fun _ => 0)
  exact hn hp

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedConsistency
