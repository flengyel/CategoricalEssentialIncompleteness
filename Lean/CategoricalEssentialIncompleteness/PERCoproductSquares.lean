/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PERCoproducts
public import CategoricalEssentialIncompleteness.PERPullbacks

/-!
# Pullback squares for the coproduct of terminal PERs

The map to the coproduct of two terminal objects records the summand of a
representative. Its fibers are the original summands. Decoding the second coordinate
gives the mediating morphisms in the two pullback squares.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def coproductToUnitsRepresentative (R S : NumericalPER) :
    Representative (coproduct R S) (coproduct unitPER unitPER) where
  val n := Part.some (Nat.pair (Nat.unpair n).1 0)
  computable := (Primrec₂.natPair.to_comp.comp
    (Computable.fst.comp Computable.unpair) (Computable.const 0)).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    rintro n m a b (⟨hn, hm, h⟩ | ⟨hn, hm, h⟩) ha hb
    all_goals
      obtain rfl := Part.mem_some_iff.mp ha
      obtain rfl := Part.mem_some_iff.mp hb
      simp [coproduct, hn, hm, unitPER]

def coproductToUnits (R S : NumericalPER) : coproduct R S ⟶ coproduct unitPER unitPER :=
  ofRepresentative (coproductToUnitsRepresentative R S)

@[simp] theorem inl_coproductToUnits (R S : NumericalPER) :
    inl R S ≫ coproductToUnits R S = ofRepresentative (unitRepresentative R) ≫
      inl unitPER unitPER := by
  apply Quotient.sound
  apply Representative.equiv_of_val_eq
  funext n
  simp [Representative.compose, inlRepresentative, coproductToUnitsRepresentative,
    unitRepresentative]

@[simp] theorem inr_coproductToUnits (R S : NumericalPER) :
    inr R S ≫ coproductToUnits R S = ofRepresentative (unitRepresentative S) ≫
      inr unitPER unitPER := by
  apply Quotient.sound
  apply Representative.equiv_of_val_eq
  funext n
  simp [Representative.compose, inrRepresentative, coproductToUnitsRepresentative,
    unitRepresentative]

def leftComponentRepresentative {W R S : NumericalPER} (f : Representative W (coproduct R S))
    (hf : ∀ n ∈ W.support, ∀ a ∈ f.val n, (Nat.unpair a).1 = 0) : Representative W R where
  val n := (f.val n).map (fun a ↦ (Nat.unpair a).2)
  computable := f.computable.map
    ((Computable.snd.comp Computable.unpair).comp Computable.snd).to₂
  total := f.total
  respects := by
    intro n m a b h ha hb
    obtain ⟨x, hx, rfl⟩ := (Part.mem_map_iff _).mp ha
    obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp hb
    rcases f.respects h hx hy with h' | h'
    · exact h'.2.2
    · have := hf n (supported_left h) x hx
      omega

theorem leftComponent_fac {W R S : NumericalPER} (f : Representative W (coproduct R S))
    (hf : ∀ n ∈ W.support, ∀ a ∈ f.val n, (Nat.unpair a).1 = 0) :
    ofRepresentative (leftComponentRepresentative f hf) ≫ inl R S = ofRepresentative f := by
  apply Quotient.sound
  intro n hn a ha b hb
  obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
  obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp hx
  obtain rfl := Part.mem_some_iff.mp ha
  have hy' : Nat.pair 0 (Nat.unpair y).2 = y := by
    rw [← hf n hn y hy]
    exact Nat.pair_unpair y
  rw [hy']
  exact f.respects hn hy hb

def rightComponentRepresentative {W R S : NumericalPER} (f : Representative W (coproduct R S))
    (hf : ∀ n ∈ W.support, ∀ a ∈ f.val n, (Nat.unpair a).1 = 1) : Representative W S where
  val n := (f.val n).map (fun a ↦ (Nat.unpair a).2)
  computable := f.computable.map
    ((Computable.snd.comp Computable.unpair).comp Computable.snd).to₂
  total := f.total
  respects := by
    intro n m a b h ha hb
    obtain ⟨x, hx, rfl⟩ := (Part.mem_map_iff _).mp ha
    obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp hb
    rcases f.respects h hx hy with h' | h'
    · have := hf n (supported_left h) x hx
      omega
    · exact h'.2.2

theorem rightComponent_fac {W R S : NumericalPER} (f : Representative W (coproduct R S))
    (hf : ∀ n ∈ W.support, ∀ a ∈ f.val n, (Nat.unpair a).1 = 1) :
    ofRepresentative (rightComponentRepresentative f hf) ≫ inr R S = ofRepresentative f := by
  apply Quotient.sound
  intro n hn a ha b hb
  obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
  obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp hx
  obtain rfl := Part.mem_some_iff.mp ha
  have hy' : Nat.pair 1 (Nat.unpair y).2 = y := by
    rw [← hf n hn y hy]
    exact Nat.pair_unpair y
  rw [hy']
  exact f.respects hn hy hb

theorem left_fiber_tag {W R S : NumericalPER} (f : Representative W (coproduct R S))
    (hf : ofRepresentative f ≫ coproductToUnits R S =
      ofRepresentative (unitRepresentative W) ≫ inl unitPER unitPER)
    (n : ℕ) (hn : n ∈ W.support) (a : ℕ) (ha : a ∈ f.val n) :
    (Nat.unpair a).1 = 0 := by
  have he := (ofRepresentative_eq_iff _ _).mp hf n hn
    (Nat.pair (Nat.unpair a).1 0) (Part.mem_bind ha (Part.mem_some _))
    (Nat.pair 0 0) (Part.mem_bind (Part.mem_some 0) (Part.mem_some _))
  rcases he with h | h
  · simpa only [Nat.unpair_pair] using h.1
  · simpa only [Nat.unpair_pair, Nat.zero_ne_one] using h.2.1

theorem right_fiber_tag {W R S : NumericalPER} (f : Representative W (coproduct R S))
    (hf : ofRepresentative f ≫ coproductToUnits R S =
      ofRepresentative (unitRepresentative W) ≫ inr unitPER unitPER)
    (n : ℕ) (hn : n ∈ W.support) (a : ℕ) (ha : a ∈ f.val n) :
    (Nat.unpair a).1 = 1 := by
  have he := (ofRepresentative_eq_iff _ _).mp hf n hn
    (Nat.pair (Nat.unpair a).1 0) (Part.mem_bind ha (Part.mem_some _))
    (Nat.pair 1 0) (Part.mem_bind (Part.mem_some 0) (Part.mem_some _))
  rcases he with h | h
  · simpa only [Nat.unpair_pair, Nat.one_ne_zero] using h.2.1
  · simpa only [Nat.unpair_pair] using h.1

theorem coproduct_to_units_inl_isPullback (R S : NumericalPER) :
    IsPullback (inl R S) (ofRepresentative (unitRepresentative R))
      (coproductToUnits R S) (inl unitPER unitPER) := by
  refine ⟨⟨inl_coproductToUnits R S⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
  intro s
  let k := (Quotient.exists_rep s.fst).choose
  have hk : ofRepresentative k = s.fst := (Quotient.exists_rep s.fst).choose_spec
  have hs : ofRepresentative k ≫ coproductToUnits R S =
      ofRepresentative (unitRepresentative s.pt) ≫ inl unitPER unitPER := by
    rw [hk, s.condition, unitIsTerminal.hom_ext s.snd
      (ofRepresentative (unitRepresentative s.pt))]
  let l := ofRepresentative (leftComponentRepresentative k (left_fiber_tag k hs))
  have hl : l ≫ inl R S = s.fst := (leftComponent_fac k (left_fiber_tag k hs)).trans hk
  refine ⟨l, hl, unitIsTerminal.hom_ext _ _, ?_⟩
  intro m hm _
  exact (cancel_mono (inl R S)).mp (hm.trans hl.symm)

theorem coproduct_to_units_inr_isPullback (R S : NumericalPER) :
    IsPullback (inr R S) (ofRepresentative (unitRepresentative S))
      (coproductToUnits R S) (inr unitPER unitPER) := by
  refine ⟨⟨inr_coproductToUnits R S⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
  intro s
  let k := (Quotient.exists_rep s.fst).choose
  have hk : ofRepresentative k = s.fst := (Quotient.exists_rep s.fst).choose_spec
  have hs : ofRepresentative k ≫ coproductToUnits R S =
      ofRepresentative (unitRepresentative s.pt) ≫ inr unitPER unitPER := by
    rw [hk, s.condition, unitIsTerminal.hom_ext s.snd
      (ofRepresentative (unitRepresentative s.pt))]
  let l := ofRepresentative (rightComponentRepresentative k (right_fiber_tag k hs))
  have hl : l ≫ inr R S = s.fst := (rightComponent_fac k (right_fiber_tag k hs)).trans hk
  refine ⟨l, hl, unitIsTerminal.hom_ext _ _, ?_⟩
  intro m hm _
  exact (cancel_mono (inr R S)).mp (hm.trans hl.symm)

/-- The injection squares for any map of binary coproducts into the two terminal summands. -/
theorem coproduct_to_units_squares {R S : NumericalPER}
    (α : R ⟶ unitPER) (β : S ⟶ unitPER)
    (f : coproduct R S ⟶ coproduct unitPER unitPER)
    (hl : α ≫ inl unitPER unitPER = inl R S ≫ f)
    (hr : β ≫ inr unitPER unitPER = inr R S ≫ f) :
    IsPullback (inl R S) α f (inl unitPER unitPER) ∧
      IsPullback (inr R S) β f (inr unitPER unitPER) := by
  have hα : α = ofRepresentative (unitRepresentative R) := unitIsTerminal.hom_ext _ _
  have hβ : β = ofRepresentative (unitRepresentative S) := unitIsTerminal.hom_ext _ _
  subst α; subst β
  have hf : f = coproductToUnits R S := coproduct_hom_ext
    (hl.symm.trans (inl_coproductToUnits R S).symm)
    (hr.symm.trans (inr_coproductToUnits R S).symm)
  subst f
  exact ⟨coproduct_to_units_inl_isPullback R S, coproduct_to_units_inr_isPullback R S⟩

end NumericalPER
end CategoricalEssentialIncompleteness
