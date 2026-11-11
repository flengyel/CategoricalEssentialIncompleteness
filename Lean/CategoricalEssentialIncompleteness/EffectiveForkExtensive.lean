/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableExtensive
public import CategoricalEssentialIncompleteness.EffectiveForkRegular

/-! # Extensivity of the actual total fork category -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

instance totalFinitaryExtensive : FinitaryExtensive Total := by
  letI : totalFunctor.IsEquivalence := totalEquivalence.isEquivalence_functor
  exact finitaryExtensive_of_preserves_and_reflects_isomorphism totalFunctor

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
