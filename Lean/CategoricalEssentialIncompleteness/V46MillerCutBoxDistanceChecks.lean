/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutBoxDistance


/-! # Finite-box distances and their positive loci -/

@[expose] public section
noncomputable section
open scoped BigOperators
open CategoricalEssentialIncompleteness.V46.Miller

example (e m t : ℕ) (z : Point) :
    0<Cut.Distance.delta e m t z ↔ z∉rho '' (Cut.haltingStage e m t)ᶜ :=
  Cut.Distance.delta_pos_iff e m t z

example (e m t : ℕ) (h : Cut.badImage e m t=∅) (z : Point) :
    Cut.Distance.delta e m t z=1 := Cut.Distance.delta_empty e m t h z

example (e m t : ℕ) (h : (Cut.badImage e m t).Nonempty) (z : Point) :
    (∃w∈Cut.badImage e m t,
      (∑'n,(1/2/(2:ℝ)^n)*|(z n:ℝ)-(w n:ℝ)|)=Cut.Distance.delta e m t z) ∧
    ∀w∈Cut.badImage e m t,Cut.Distance.delta e m t z≤
      ∑'n,(1/2/(2:ℝ)^n)*|(z n:ℝ)-(w n:ℝ)| :=
  Cut.Distance.delta_nonempty_minimum e m t h z

example (e m t : ℕ) : Continuous (Cut.Distance.delta e m t) := Cut.Distance.continuous_delta e m t
example (e m t : ℕ) (z : Point) :
    0≤Cut.Distance.delta e m t z ∧ Cut.Distance.delta e m t z≤1 := Cut.Distance.delta_bounds e m t z
