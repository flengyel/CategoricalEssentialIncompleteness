/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalSubobjects

/-!
# Unions of enumerable PER supports

Dovetailing semidecision procedures gives a factorization through every common
upper bound of two c.e. support inclusions. Thus their union represents their
categorical join. The computable choice of summand uses enumerability of both supports.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

private theorem union_representative {A B X : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hAX : A ⊆ X) (hBX : B ⊆ X) {R : NumericalPER}
    (a : Representative (discrete A) R) (b : Representative (discrete B) R)
    (m : Representative R (discrete X))
    (ha : ofRepresentative a ≫ ofRepresentative m = inclusion hAX)
    (hb : ofRepresentative b ≫ ofRepresentative m = inclusion hBX) :
    ∃ k : Representative (discrete (A ∪ B)) R,
      ofRepresentative k ≫ ofRepresentative m = inclusion (Set.union_subset hAX hBX) := by
  let fa : ℕ → Part ℕ := fun n ↦ (supportIdentity A n).bind a.val
  let fb : ℕ → Part ℕ := fun n ↦ (supportIdentity B n).bind b.val
  have hfa : Partrec fa :=
    (supportIdentity_partrec A hA).bind (a.computable.comp Computable.snd).to₂
  have hfb : Partrec fb :=
    (supportIdentity_partrec B hB).bind (b.computable.comp Computable.snd).to₂
  have hfa_mem : ∀ n z, z ∈ fa n ↔ n ∈ A ∧ z ∈ a.val n := by
    intro n z
    simp only [fa, Part.mem_bind_iff, mem_supportIdentity]
    constructor
    · rintro ⟨i, ⟨hn, rfl⟩, hz⟩; exact ⟨hn, hz⟩
    · rintro ⟨hn, hz⟩; exact ⟨n, ⟨hn, rfl⟩, hz⟩
  have hfb_mem : ∀ n z, z ∈ fb n ↔ n ∈ B ∧ z ∈ b.val n := by
    intro n z
    simp only [fb, Part.mem_bind_iff, mem_supportIdentity]
    constructor
    · rintro ⟨i, ⟨hn, rfl⟩, hz⟩; exact ⟨hn, hz⟩
    · rintro ⟨hn, hz⟩; exact ⟨n, ⟨hn, rfl⟩, hz⟩
  obtain ⟨k, hk, h⟩ := Partrec.merge' hfa hfb
  have supported : ∀ n z, z ∈ k n → z ∈ R.support := by
    intro n z hz
    rcases (h n).1 z hz with hz | hz
    · obtain ⟨hn, hz⟩ := (hfa_mem n z).mp hz
      exact a.output_supported ⟨hn, rfl⟩ hz
    · obtain ⟨hn, hz⟩ := (hfb_mem n z).mp hz
      exact b.output_supported ⟨hn, rfl⟩ hz
  let t : Representative (discrete (A ∪ B)) R :=
    { val := k
      computable := hk
      total := by
        intro n hn
        apply (h n).2.mpr
        rcases hn.1 with hn | hn
        · exact Or.inl (Part.dom_iff_mem.mpr ⟨_,
            (hfa_mem _ _).mpr ⟨hn, Part.get_mem (a.total n ⟨hn, rfl⟩)⟩⟩)
        · exact Or.inr (Part.dom_iff_mem.mpr ⟨_,
            (hfb_mem _ _).mpr ⟨hn, Part.get_mem (b.total n ⟨hn, rfl⟩)⟩⟩)
      respects := by
        intro n l u v hn hu hv
        obtain ⟨_, rfl⟩ := hn
        have heq := Part.mem_unique hu hv
        exact heq ▸ supported n u hu }
  refine ⟨t, ?_⟩
  apply (ofRepresentative_eq_iff _ _).mpr
  intro n _ z hz y hy
  have hyEq : y = n := Part.mem_some_iff.mp hy
  subst y
  obtain ⟨u, hu, hz⟩ := Part.mem_bind_iff.mp hz
  rcases (h n).1 u hu with hu | hu
  · obtain ⟨hnA, hu⟩ := (hfa_mem n u).mp hu
    exact (ofRepresentative_eq_iff _ _).mp ha n ⟨hnA, rfl⟩ z
      (Part.mem_bind hu hz) n (Part.mem_some n)
  · obtain ⟨hnB, hu⟩ := (hfb_mem n u).mp hu
    exact (ofRepresentative_eq_iff _ _).mp hb n ⟨hnB, rfl⟩ z
      (Part.mem_bind hu hz) n (Part.mem_some n)

theorem enumerable_union_lift {A B X : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hAX : A ⊆ X) (hBX : B ⊆ X) {R : NumericalPER}
    (a : discrete A ⟶ R) (b : discrete B ⟶ R) (m : R ⟶ discrete X)
    (ha : a ≫ m = inclusion hAX) (hb : b ≫ m = inclusion hBX) :
    ∃ k : discrete (A ∪ B) ⟶ R, k ≫ m = inclusion (Set.union_subset hAX hBX) := by
  revert ha hb
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      induction m using Quotient.inductionOn with | _ m =>
        intro ha hb
        obtain ⟨k, hk⟩ := union_representative hA hB hAX hBX a b m ha hb
        exact ⟨ofRepresentative k, hk⟩

/-- The union is the least upper bound among all categorical subobjects. -/
theorem enumerable_union_isLUB {A B X : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) (hAX : A ⊆ X) (hBX : B ⊆ X) :
    IsLUB {supportSubobject A hAX, supportSubobject B hBX}
      (supportSubobject (A ∪ B) (Set.union_subset hAX hBX)) := by
  constructor
  · intro P hP
    rcases hP with rfl | rfl
    · exact (supportSubobject_le_iff _ _).mpr Set.subset_union_left
    · exact (supportSubobject_le_iff _ _).mpr Set.subset_union_right
  · intro P hP
    have ha := hP (Set.mem_insert _ _)
    have hb := hP (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨k, hk⟩ := enumerable_union_lift hA hB hAX hBX
      (Subobject.ofMkLE (inclusion hAX) P ha)
      (Subobject.ofMkLE (inclusion hBX) P hb) P.arrow
      (Subobject.ofMkLE_arrow ha) (Subobject.ofMkLE_arrow hb)
    simpa only [supportSubobject, Subobject.mk_arrow] using Subobject.mk_le_mk_of_comm k hk

end NumericalPER
end CategoricalEssentialIncompleteness
