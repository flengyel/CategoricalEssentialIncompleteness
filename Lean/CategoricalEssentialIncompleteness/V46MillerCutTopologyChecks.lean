/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutTopology


/-! # Statement checks in `V46MillerCutTopologyChecks` -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller

example : Primrec Cut.complementWords := Cut.complementWords_primrec
example (L : List Word) : (Cut.cylinderUnion L)ᶜ = Cut.cylinderUnion (Cut.complementWords L) :=
  Cut.complement_cylinderUnion L
example (e m t : ℕ) : Cut.badImage e m t = rho '' (Cut.haltingStage e m t)ᶜ := rfl
example (e m t : ℕ) : IsCompact (Cut.badImage e m t) ∧ IsClosed (Cut.badImage e m t) :=
  ⟨Cut.badImage_isCompact e m t,Cut.badImage_isClosed e m t⟩
example (e m : ℕ) (z : Point) :
    (∃ t, z ∈ (rho '' (Cut.haltingStage e m t)ᶜ)ᶜ) ↔ m ∈ Unanimity.tau z e e :=
  Cut.openStage_iff_tau e m z
example (e i : ℕ) : Cut.side e i = ⋃ m : ℕ, ⋃ (_ : m % 2 = i), ⋃ t : ℕ, Cut.openStage e m t :=
  Cut.side_union e i
example (e : ℕ) : Disjoint (Cut.side e 0) (Cut.side e 1) := Cut.side_disjoint e
