/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalTuplesPartialMaps
public import CategoricalEssentialIncompleteness.EffectiveForkExtensive
public import CategoricalEssentialIncompleteness.EffectiveForkSpans

/-! # The numerical tuple presentation of total effective forks -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.NumericalTuples

/-- The actual total fork category is equivalent to diagrams of numerical tuples. -/
def forkEquivalence : EffectiveFork.Total ≌ (WalkingSpan ⥤ Object) :=
  EffectiveFork.totalEquivalence.trans (equivalence.symm.congrRight (E := WalkingSpan))

end CategoricalEssentialIncompleteness.V46.NumericalTuples
