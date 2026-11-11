/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkComparison

/-! # Explicit three-point comparison statements -/

@[expose] public section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

noncomputable section

example (c c' : Idem EffectiveFork.Recursion.U) (hc : Complementary c c') :
    ∃ ℓ : EffectiveFork.Recursion.U ⟶
        coprod EffectiveFork.Recursion.U EffectiveFork.Recursion.U,
      isTotal ℓ ∧ c.hom ≫ ℓ = c.hom ≫ i1 _ _ ∧
        c'.hom ≫ ℓ = c'.hom ≫ i0 _ _ :=
  EffectiveFork.Recursion.complementary_conditionals_v46 c c' hc

example : Inseparable EffectiveFork.Recursion.pair0 EffectiveFork.Recursion.pair1 :=
  EffectiveFork.Recursion.pair_inseparable_v46

example : Inseparable
    (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair0)
    (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair1) :=
  EffectiveFork.Recursion.image_pair_inseparable_v46

example (t : Idem ForkSyntax.S) (ht : ForkSyntax.categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull ForkSyntax.nu t = ⊥) :
    Inseparable t (Idem.pull ForkSyntax.nu t) ∧
      t ⊔ Idem.pull ForkSyntax.nu t ≠ ⊤ :=
  ForkSyntax.essential_incompleteness_v46 t ht hc
