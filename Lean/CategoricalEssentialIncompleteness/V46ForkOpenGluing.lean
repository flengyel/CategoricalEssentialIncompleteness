/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkTopology
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.ContinuousMap.Basic

/-! # The two open Sierpiński subspaces of the fork -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Topology
namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

/-- The two-point Sierpiński space, with one open singleton. -/
inductive SierpinskiPoint where
  | closedPoint | openPoint
  deriving DecidableEq, Fintype

open SierpinskiPoint

instance : TopologicalSpace SierpinskiPoint where
  IsOpen U := closedPoint ∈ U → openPoint ∈ U
  isOpen_univ := fun _ => trivial
  isOpen_inter _ _ hu hv := fun h => ⟨hu h.1, hv h.2⟩
  isOpen_sUnion _ H := fun ⟨u, hu, hx⟩ => ⟨u, hu, H u hu hx⟩

def inclusion (i : Bool) : SierpinskiPoint → Point
  | closedPoint => if i then .b else .a
  | openPoint => .c

theorem inclusion_openEmbedding (i : Bool) : IsOpenEmbedding (inclusion i) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply continuous_def.mpr
    intro u hu
    change inclusion i closedPoint ∈ u → Point.c ∈ u
    cases i
    · exact hu.1
    · exact hu.2
  · intro x y h
    cases i <;> cases x <;> cases y <;> simp_all [inclusion]
  · intro u hu
    have h : closedPoint ∈ u → openPoint ∈ u := hu
    change (Point.a ∈ inclusion i '' u → Point.c ∈ inclusion i '' u) ∧
      (Point.b ∈ inclusion i '' u → Point.c ∈ inclusion i '' u)
    constructor <;> rintro ⟨x, hx, e⟩ <;> refine ⟨openPoint, ?_, rfl⟩ <;>
      cases x <;> first | exact h hx | exact hx

/-- The induced topology on each image is the Sierpiński topology. -/
noncomputable def sideHomeomorphism (i : Bool) : SierpinskiPoint ≃ₜ Set.range (inclusion i) :=
  (inclusion_openEmbedding i).toIsEmbedding.toHomeomorph

theorem range_inclusion (i : Bool) :
    Set.range (inclusion i) = ((if i then Open.R else Open.L).toActual : Set Point) := by
  ext x
  change (∃ y, inclusion i y = x) ↔ x ∈ (if i then Open.R else Open.L)
  cases i <;> cases x <;> decide

/-- Continuous maps on the two sides extend uniquely when their open points agree. -/
theorem existsUnique_gluing {Y : Type*} [TopologicalSpace Y]
    (f g : C(SierpinskiPoint, Y)) (agree : f openPoint = g openPoint) :
    ∃! h : C(Point, Y), (∀ x, h (inclusion false x) = f x) ∧
      (∀ x, h (inclusion true x) = g x) := by
  let h : Point → Y
    | .a => f closedPoint
    | .b => g closedPoint
    | .c => f openPoint
  have hh : Continuous h := by
    apply continuous_def.mpr
    intro u hu
    have hf : f closedPoint ∈ u → f openPoint ∈ u := hu.preimage f.continuous
    have hg : g closedPoint ∈ u → g openPoint ∈ u := hu.preimage g.continuous
    change (f closedPoint ∈ u → f openPoint ∈ u) ∧ (g closedPoint ∈ u → f openPoint ∈ u)
    exact ⟨hf, fun hgu => agree.symm ▸ hg hgu⟩
  refine ⟨⟨h, hh⟩, ⟨(fun x => by cases x <;> rfl), (fun x => by cases x; rfl; exact agree)⟩, ?_⟩
  intro k hk
  apply ContinuousMap.ext
  intro x
  cases x
  · exact hk.1 closedPoint
  · exact hk.2 closedPoint
  · exact hk.1 openPoint

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
