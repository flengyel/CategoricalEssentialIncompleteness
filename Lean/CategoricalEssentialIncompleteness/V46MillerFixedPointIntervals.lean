/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerFixedPointCertificates
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.Compact

/-! # Closed interval correspondences on the Hilbert cube

At a point of the cube collect the values of all its binary names and
take their interval hull. The resulting coordinate graph is closed.
-/

@[expose] public section
noncomputable section

open Set
namespace CategoricalEssentialIncompleteness.V46.Miller

private def valuesAt (d : ℕ) (a : Point) : Set UnitInterval :=
  {x | ∃ p, rho p = a ∧ x ∈ nameInterval d p}

private theorem values_graph_closed (d : ℕ) :
    IsClosed {z : Point × UnitInterval | z.2 ∈ valuesAt d z.1} := by
  let f : Bits × UnitInterval → Point × UnitInterval := fun z => (rho z.1, z.2)
  have hf : Continuous f := (rho_continuous.comp continuous_fst).prodMk continuous_snd
  have he : {z : Point × UnitInterval | z.2 ∈ valuesAt d z.1} =
      f '' {z : Bits × UnitInterval | z.2 ∈ nameInterval d z.1} := by
    ext ⟨a, x⟩
    constructor
    · rintro ⟨p, rfl, hp⟩
      exact ⟨(p, x), hp, rfl⟩
    · rintro ⟨⟨p, y⟩, hp, h⟩
      cases h
      exact ⟨p, rfl, hp⟩
  rw [he]
  exact ((nameInterval_graph_closed d).isCompact.image hf).isClosed

private theorem values_nonempty (d : ℕ) (a : Point) : (valuesAt d a).Nonempty := by
  obtain ⟨p, rfl⟩ := rho_surjective a
  obtain ⟨x, hx⟩ := nameInterval_nonempty d p
  exact ⟨x, p, rfl, hx⟩

/-- Interval hull of the values for a program index over the binary names of a point. -/
@[no_expose] def coordinateInterval (d : ℕ) (a : Point) : Set UnitInterval :=
  {x | ∃ l ∈ valuesAt d a, ∃ u ∈ valuesAt d a, l ≤ x ∧ x ≤ u}

theorem coordinateInterval_box (d : ℕ) (a : Point) :
    ∃ l u : UnitInterval, l ≤ u ∧ coordinateInterval d a = Icc l u := by
  have hc : IsCompact (valuesAt d a) :=
    ((values_graph_closed d).preimage (continuous_const.prodMk continuous_id)).isCompact
  obtain ⟨l, hl⟩ := hc.exists_isLeast (values_nonempty d a)
  obtain ⟨u, hu⟩ := hc.exists_isGreatest (values_nonempty d a)
  refine ⟨l, u, hl.2 hu.1, Set.ext fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨v, hv, w, hw, hvx, hxw⟩
    exact ⟨(hl.2 hv).trans hvx, hxw.trans (hu.2 hw)⟩
  · rintro ⟨hlx, hxu⟩
    exact ⟨l, hl.1, u, hu.1, hlx, hxu⟩

theorem coordinateInterval_graph_closed (d : ℕ) :
    IsClosed {z : Point × UnitInterval | z.2 ∈ coordinateInterval d z.1} := by
  let W := (Point × UnitInterval) × (UnitInterval × UnitInterval)
  let s : Set W := {z | z.2.1 ∈ valuesAt d z.1.1 ∧ z.2.2 ∈ valuesAt d z.1.1 ∧
    z.2.1 ≤ z.1.2 ∧ z.1.2 ≤ z.2.2}
  have h₁ : Continuous (fun z : W => z.1.1) := continuous_fst.comp continuous_fst
  have hx : Continuous (fun z : W => z.1.2) := continuous_snd.comp continuous_fst
  have hl : Continuous (fun z : W => z.2.1) := continuous_fst.comp continuous_snd
  have hu : Continuous (fun z : W => z.2.2) := continuous_snd.comp continuous_snd
  have hs : IsClosed s := ((values_graph_closed d).preimage (h₁.prodMk hl)).inter
    (((values_graph_closed d).preimage (h₁.prodMk hu)).inter
      ((isClosed_le (continuous_subtype_val.comp hl) (continuous_subtype_val.comp hx)).inter
        (isClosed_le (continuous_subtype_val.comp hx) (continuous_subtype_val.comp hu))))
  have he : {z : Point × UnitInterval | z.2 ∈ coordinateInterval d z.1} = Prod.fst '' s := by
    ext ⟨a, x⟩
    constructor
    · rintro ⟨l, hl', u, hu', hlx, hxu⟩
      exact ⟨((a, x), (l, u)), ⟨hl', hu', hlx, hxu⟩, rfl⟩
    · rintro ⟨⟨_, l, u⟩, h, rfl⟩
      exact ⟨l, h.1, u, h.2.1, h.2.2⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ hs

theorem coordinateInterval_singleton {d : ℕ} {a : Point} {r : UnitInterval}
    (h : ∀ p ∈ representations a, ComputesReal d p r) : coordinateInterval d a = {r} := by
  have eqr : ∀ {x}, x ∈ valuesAt d a → x = r := by
    rintro x ⟨p, hp, hx⟩
    simpa only [nameInterval_singleton (h p hp), mem_singleton_iff] using hx
  obtain ⟨v, hv⟩ := values_nonempty d a
  have hr : r ∈ valuesAt d a := eqr hv ▸ hv
  ext x
  constructor
  · rintro ⟨l, hl, u, hu, hlx, hxu⟩
    rw [eqr hl] at hlx
    rw [eqr hu] at hxu
    exact mem_singleton_iff.mpr (le_antisymm hxu hlx)
  · intro hx
    obtain rfl : x = r := mem_singleton_iff.mp hx
    exact ⟨_, hr, _, hr, le_rfl, le_rfl⟩

/-- A point belonging to every coordinate interval satisfies the Miller property
for the chosen oracle interpreter and the chosen rational enumeration. -/
theorem isMiller_of_coordinate_mem {a : Point} (ha : ∀ d, a d ∈ coordinateInterval d a) :
    IsMiller a := by
  intro d r h
  simpa only [coordinateInterval_singleton h, mem_singleton_iff] using ha d

end CategoricalEssentialIncompleteness.V46.Miller
