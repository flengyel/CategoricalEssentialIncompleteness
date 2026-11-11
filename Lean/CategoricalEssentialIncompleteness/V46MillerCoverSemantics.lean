/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDyadicSeparation
public import CategoricalEssentialIncompleteness.V46MillerFiniteCover
public import CategoricalEssentialIncompleteness.V46MillerOracleProgramEffective

/-! # Finite covers characterize unanimity on the full representation fiber -/

@[expose] public section
noncomputable section
open Set Encodable Denumerable
namespace CategoricalEssentialIncompleteness.V46.Miller.Unanimity

abbrev Input := ℕ × ℕ

def Unanimous (z : Point) (a : Input) (m : ℕ) : Prop :=
  ∀ q ∈ representations z, m ∈ OracleProgram.numberedEval a.1 q a.2

def HaltsOn (a : Input) (m : ℕ) (s : Word) : Prop :=
  OracleProgram.HaltingCylinder (((ofNat OracleProgram.Code a.1,a.2),m),s)

def Good (u : Word) (a : Input) (m : ℕ) (s : Word) : Prop :=
  HaltsOn a m s ∨ ∃ n k, ApartAt u s n k

def Certified (u : Word) (a : Input) (m : ℕ) : Prop :=
  ∃ L : List Word, FiniteCover.covers L = true ∧ ∀ s ∈ L, Good u a m s

theorem good_mono (u v : Word) (h : u <+: v) (a : Input) (m : ℕ) (s : Word) :
    Good u a m s → Good v a m s := by
  rintro (hh | ⟨n,k,hk⟩)
  · exact Or.inl hh
  · exact Or.inr ⟨n,k,apartAt_mono_left u v s n k h hk⟩

theorem certified_mono (u v : Word) (h : u <+: v) (a : Input) (m : ℕ) :
    Certified u a m → Certified v a m := by
  rintro ⟨L,hL,hG⟩
  exact ⟨L,hL,fun s hs => good_mono u v h a m s (hG s hs)⟩

theorem certified_sound (u : Word) (a : Input) (m : ℕ) (h : Certified u a m)
    (p : Bits) (hp : p ∈ cylinder u) : Unanimous (rho p) a m := by
  intro q hq
  obtain ⟨L,hL,hG⟩ := h
  obtain ⟨s,hs,hqs⟩ := (FiniteCover.covers_iff L).mp hL q
  rcases hG s hs with hh | ⟨n,k,hk⟩
  · exact (OracleProgram.eval_cylinders (ofNat OracleProgram.Code a.1) q a.2 m).mpr
      ⟨s,hh,hqs⟩
  · exact False.elim ((apartAt_sound u s n k hk p q hp hqs) hq.symm)

theorem certified_unique (u : Word) (a : Input) (m m' : ℕ)
    (hm : Certified u a m) (hm' : Certified u a m') : m = m' := by
  let p := extend u
  have hp : p ∈ cylinder u := prefix_extend u
  exact Part.mem_unique (certified_sound u a m hm p hp p rfl)
    (certified_sound u a m' hm' p hp p rfl)

def GoodFor (p : Bits) (a : Input) (m : ℕ) (s : Word) : Prop :=
  ∃ r, Good (bitPrefix p r) a m s

theorem goodFor_cover (p : Bits) (a : Input) (m : ℕ)
    (h : Unanimous (rho p) a m) (q : Bits) :
    ∃ s, GoodFor p a m s ∧ q ∈ cylinder s := by
  classical
  by_cases he : rho q = rho p
  · obtain ⟨s,hs,hq⟩ := (OracleProgram.eval_cylinders
      (ofNat OracleProgram.Code a.1) q a.2 m).mp (h q he)
    exact ⟨s,⟨0,Or.inl hs⟩,hq⟩
  · obtain ⟨n,k,hk⟩ := exists_apartAt p q (fun h => he h.symm)
    exact ⟨bitPrefix q (queryBound n k),
      ⟨queryBound n k,Or.inr ⟨n,k,hk⟩⟩,mem_cylinder_prefix q _⟩

theorem finite_good_cover (p : Bits) (a : Input) (m : ℕ)
    (h : Unanimous (rho p) a m) :
    ∃ L : List Word, FiniteCover.covers L = true ∧ ∀ s ∈ L, GoodFor p a m s := by
  classical
  let U : Word → Set Bits := fun s => if GoodFor p a m s then cylinder s else ∅
  have hU : ∀ s, IsOpen (U s) := by
    intro s
    by_cases hs : GoodFor p a m s
    · simpa only [U,ite_eq_left hs] using cylinder_isOpen s
    · simp only [U,ite_eq_right hs,isOpen_empty]
  have hcover : (Set.univ : Set Bits) ⊆ ⋃ s, U s := by
    intro q _
    obtain ⟨s,hg,hq⟩ := goodFor_cover p a m h q
    exact Set.mem_iUnion.mpr ⟨s,by simpa only [U,ite_eq_left hg] using hq⟩
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let L := (t.filter (GoodFor p a m)).toList
  refine ⟨L,(FiniteCover.covers_iff L).mpr ?_,?_⟩
  · intro q
    obtain ⟨s,hs,hqs⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ q))
    have hg : GoodFor p a m s := by
      by_contra hg
      simp only [U,ite_eq_right hg,Set.mem_empty_iff_false] at hqs
    refine ⟨s,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hs,hg⟩),?_⟩
    simpa only [U,ite_eq_left hg] using hqs
  · intro s hs
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hs)).2

theorem finite_prefix_bound (p : Bits) (a : Input) (m : ℕ) (L : List Word)
    (h : ∀ s ∈ L, GoodFor p a m s) :
    ∃ r, ∀ s ∈ L, Good (bitPrefix p r) a m s := by
  induction L with
  | nil => exact ⟨0,by simp⟩
  | cons s L ih =>
    obtain ⟨r,hr⟩ := h s (by simp)
    obtain ⟨t,ht⟩ := ih (fun u hu => h u (List.mem_cons_of_mem s hu))
    refine ⟨max r t,?_⟩
    intro u hu
    obtain rfl | hu := List.mem_cons.mp hu
    · exact good_mono _ _ (bitPrefix_isPrefix p (le_max_left r t)) a m _ hr
    · exact good_mono _ _ (bitPrefix_isPrefix p (le_max_right r t)) a m u (ht u hu)

theorem search_correct (p : Bits) (a : Input) (m : ℕ) :
    (∃ r, Certified (bitPrefix p r) a m) ↔ Unanimous (rho p) a m := by
  constructor
  · rintro ⟨r,hr⟩
    exact certified_sound _ a m hr p (mem_cylinder_prefix p r)
  · intro h
    obtain ⟨L,hL,hG⟩ := finite_good_cover p a m h
    obtain ⟨r,hr⟩ := finite_prefix_bound p a m L hG
    exact ⟨r,L,hL,hr⟩

end CategoricalEssentialIncompleteness.V46.Miller.Unanimity
