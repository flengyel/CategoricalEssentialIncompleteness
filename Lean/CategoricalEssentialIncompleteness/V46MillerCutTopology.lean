/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutStages

/-! # Compact bad images and the open parity regions

This proves the finite-stage and compactness part of Lemma 9.3 using the literal
oracle programs, binary cylinders, rho, and tau. It also gives an explicit
primitive-recursive finite-cylinder presentation of each complement.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut

/-- Complete all words to the computed common depth, then retain exactly
the uncovered words. This includes the zero-depth and empty-list cases. -/
def complementWords (L : List Word) : List Word :=
  (FiniteCover.words (FiniteCover.depth L)).filter
    (fun s => ¬ FiniteCover.coveredAt L s)

theorem complementWords_primrec : Primrec complementWords := by
  have hR : PrimrecRel (fun s : Word => fun L : List Word => ¬ FiniteCover.coveredAt L s) :=
    FiniteCover.coveredAt_primrec.swap.not
  exact ((PrimrecRel.listFilter hR).comp
    (FiniteCover.words_primrec.comp FiniteCover.depth_primrec) Primrec.id).of_eq
      (fun _ => rfl)

private theorem coveredAt_prefix_iff (L : List Word) (p : Bits) :
    FiniteCover.coveredAt L (bitPrefix p (FiniteCover.depth L)) ↔ p ∈ cylinderUnion L := by
  constructor
  · rintro ⟨s,hs,hst⟩
    refine ⟨s,hs,?_⟩
    change bitPrefix p s.length = s
    exact (FiniteCover.take_prefix p (FiniteCover.length_le_depth hs)).symm.trans hst
  · rintro ⟨s,hs,hp⟩
    change bitPrefix p s.length = s at hp
    exact ⟨s,hs,(FiniteCover.take_prefix p (FiniteCover.length_le_depth hs)).trans hp⟩

/-- A constructor-level finite-cylinder complement calculation. -/
theorem complement_cylinderUnion (L : List Word) :
    (cylinderUnion L)ᶜ = cylinderUnion (complementWords L) := by
  ext p
  constructor
  · intro hp
    let s := bitPrefix p (FiniteCover.depth L)
    refine ⟨s,List.mem_filter.mpr ⟨?_,?_⟩,mem_cylinder_prefix p _⟩
    · exact FiniteCover.mem_words_of_length (prefix_length p _)
    · apply decide_eq_true_iff.mpr
      exact fun hs => hp ((coveredAt_prefix_iff L p).mp hs)
  · rintro ⟨s,hs,hp⟩ hL
    obtain ⟨hs,hnot⟩ := List.mem_filter.mp hs
    have hlen : s.length = FiniteCover.depth L := FiniteCover.mem_words_length hs
    have he : bitPrefix p (FiniteCover.depth L) = s := by
      change bitPrefix p s.length = s at hp
      simpa only [hlen] using hp
    exact (of_decide_eq_true hnot) (he ▸ (coveredAt_prefix_iff L p).mpr hL)

/-- The manuscript's Closed bad set K_{e,m,t}. -/
def badImage (e m t : ℕ) : Set Point := rho '' (haltingStage e m t)ᶜ

theorem badImage_isCompact (e m t : ℕ) : IsCompact (badImage e m t) :=
  ((haltingStage_isOpen e m t).isClosed_compl.isCompact).image rho_continuous

theorem badImage_isClosed (e m t : ℕ) : IsClosed (badImage e m t) :=
  (badImage_isCompact e m t).isClosed

theorem badImage_antitone (e m : ℕ) : Antitone (badImage e m) := by
  intro t u h
  rintro z ⟨p,hp,rfl⟩
  exact ⟨p,(fun ht => hp (haltingStage_mono e m h ht)),rfl⟩

/-- The bad image is the finite union of the images of explicitly computed
binary cylinders. Identifying each image with closed dyadic boxes is a
separate real-analysis comparison. -/
theorem badImage_finite_cylinders (e m t : ℕ) :
    badImage e m t =
      ⋃ s ∈ complementWords (stageWords e m t), rho '' cylinder s := by
  change rho '' (cylinderUnion (stageWords e m t))ᶜ = _
  rw [complement_cylinderUnion]
  ext z
  constructor
  · rintro ⟨p,⟨s,hs,hp⟩,rfl⟩
    exact Set.mem_iUnion.mpr ⟨s,Set.mem_iUnion.mpr ⟨hs,⟨p,hp,rfl⟩⟩⟩
  · intro h
    obtain ⟨s,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hs,p,hp,he⟩ := Set.mem_iUnion.mp h
    exact ⟨p,⟨s,hs,hp⟩,he⟩

def openStage (e m t : ℕ) : Set Point := (badImage e m t)ᶜ

theorem openStage_isOpen (e m t : ℕ) : IsOpen (openStage e m t) :=
  (badImage_isClosed e m t).isOpen_compl

theorem openStage_mono (e m : ℕ) : Monotone (openStage e m) := by
  intro t u h z hz hu
  exact hz (badImage_antitone e m h hu)

/-- This equivalence compares the rho-image, rather than assuming that a chosen
representation decides membership in its image. -/
theorem openStage_spec (e m t : ℕ) (z : Point) :
    z ∈ openStage e m t ↔ ∀ p ∈ representations z, p ∈ haltingStage e m t := by
  constructor
  · intro hz p hp
    by_contra h
    exact hz ⟨p,h,hp⟩
  · intro hz hbad
    obtain ⟨p,hp,hpz⟩ := hbad
    exact hp (hz p hpz)

/-- Compactness supplies ONE finite stage for the entire representation
fiber, starting from the literal all-representation halting condition. -/
theorem uniform_haltingStage (e m : ℕ) (z : Point)
    (h : ∀ p ∈ representations z, m ∈ OracleProgram.numberedEval e p e) :
    ∃ t, ∀ p ∈ representations z, p ∈ haltingStage e m t := by
  classical
  have hcover : representations z ⊆ ⋃ t, haltingStage e m t := by
    intro p hp
    exact (mem_halting_union e m p).mpr (h p hp)
  obtain ⟨F,hF⟩ := (representations_isCompact z).elim_finite_subcover
    (haltingStage e m) (haltingStage_isOpen e m) hcover
  refine ⟨F.sup id,?_⟩
  intro p hp
  obtain ⟨t,ht,hpt⟩ := Set.mem_iUnion₂.mp (hF hp)
  exact haltingStage_mono e m (Finset.le_sup ht) hpt

/-- The key compactness equivalence used by the cozero construction. -/
theorem openStage_iff_tau (e m : ℕ) (z : Point) :
    (∃ t, z ∈ openStage e m t) ↔ m ∈ Unanimity.tau z e e := by
  constructor
  · rintro ⟨t,ht⟩
    apply (Unanimity.tau_graph z e e m).mpr
    intro p hp
    exact haltingStage_sound e m t p ((openStage_spec e m t z).mp ht p hp)
  · intro hm
    obtain ⟨t,ht⟩ := uniform_haltingStage e m z ((Unanimity.tau_graph z e e m).mp hm)
    exact ⟨t,(openStage_spec e m t z).mpr ht⟩

/-- The open parity regions U_e^i, with the manuscript's diagonal. -/
def side (e i : ℕ) : Set Point :=
  {z | ∃ m, m % 2 = i ∧ m ∈ Unanimity.tau z e e}

theorem side_union (e i : ℕ) :
    side e i = ⋃ m : ℕ, ⋃ (_ : m % 2 = i), ⋃ t : ℕ, openStage e m t := by
  ext z
  constructor
  · rintro ⟨m,hmpar,hm⟩
    obtain ⟨t,ht⟩ := (openStage_iff_tau e m z).mpr hm
    exact Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hmpar,Set.mem_iUnion.mpr ⟨t,ht⟩⟩⟩
  · intro h
    obtain ⟨m,h⟩ := Set.mem_iUnion.mp h
    obtain ⟨hmpar,h⟩ := Set.mem_iUnion.mp h
    exact ⟨m,hmpar,(openStage_iff_tau e m z).mp (Set.mem_iUnion.mp h)⟩

theorem side_isOpen (e i : ℕ) : IsOpen (side e i) := by
  rw [side_union]
  exact isOpen_iUnion (fun m => isOpen_iUnion (fun _ =>
    isOpen_iUnion (fun t => openStage_isOpen e m t)))

theorem side_disjoint (e : ℕ) : Disjoint (side e 0) (side e 1) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨m,hmpar,hm⟩ ⟨n,hnpar,hn⟩
  have he : m=n := Part.mem_unique hm hn
  omega

/- The two open sides are disjoint because a partial computation has at most one output. -/

end CategoricalEssentialIncompleteness.V46.Miller.Cut
