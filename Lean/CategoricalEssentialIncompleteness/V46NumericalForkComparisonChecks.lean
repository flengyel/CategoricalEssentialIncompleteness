/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalForkComparison

/-! Exact tuple diagram comparison and the existing componentwise structure. -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.NumericalTuples

example : EffectiveFork.Total ≌ (WalkingSpan ⥤ Object) := forkEquivalence
example : HasFiniteLimits Object := inferInstance
example : HasFiniteCoproducts Object := inferInstance
example : HasFiniteLimits EffectiveFork.Total := inferInstance
example : HasFiniteCoproducts EffectiveFork.Total := inferInstance
example : Regular EffectiveFork.Total := inferInstance
example : FinitaryExtensive EffectiveFork.Total := inferInstance

example {X Y : EffectiveFork.Total} (f : X ⟶ Y) :
    Mono f ↔ EffectiveFork.Injective f.hom := EffectiveFork.total_mono_iff_injective f

example {X Y : EffectiveFork.Total} (f : X ⟶ Y) :
    IsImage (EffectiveFork.imageFactorization f).toMonoFactorisation :=
  EffectiveFork.imageIsImage f
