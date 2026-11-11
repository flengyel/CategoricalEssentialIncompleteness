/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PERCoproducts
public import CategoricalEssentialIncompleteness.PERPullbacks

/-!
# Decomposition along PER coproduct injections

For an arrow into a coproduct, the copairing of its two pullback projections
is an isomorphism. Its inverse evaluates a representing function and uses the
first coordinate of its output to choose the summand. The remaining coordinates
supply a representative in the corresponding pullback.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

variable {R S T : NumericalPER}

def decompositionCode (n a : ℕ) : ℕ :=
  Nat.pair (Nat.unpair a).1 (Nat.pair n (Nat.unpair a).2)

theorem pullback_inl_supported (f : Representative R (coproduct S T))
    {n a : ℕ} (hn : n ∈ R.support) (ha : a ∈ f.val n) (ht : (Nat.unpair a).1 = 0) :
    Nat.pair n (Nat.unpair a).2 ∈ (pullbackPER f (inlRepresentative S T)).support := by
  have hs := f.output_supported hn ha
  have hS : S.rel (Nat.unpair a).2 (Nat.unpair a).2 := by
    rcases hs with h | h
    · exact h.2.2
    · omega
  have he : Nat.pair 0 (Nat.unpair a).2 = a := by rw [← ht]; exact Nat.pair_unpair a
  refine ⟨by simpa [product, support] using And.intro hn hS, ?_, ?_⟩ <;>
    exact ⟨a, by simpa using ha, a, by simp [inlRepresentative, he], hs⟩

theorem pullback_inr_supported (f : Representative R (coproduct S T))
    {n a : ℕ} (hn : n ∈ R.support) (ha : a ∈ f.val n) (ht : (Nat.unpair a).1 = 1) :
    Nat.pair n (Nat.unpair a).2 ∈ (pullbackPER f (inrRepresentative S T)).support := by
  have hs := f.output_supported hn ha
  have hT : T.rel (Nat.unpair a).2 (Nat.unpair a).2 := by
    rcases hs with h | h
    · omega
    · exact h.2.2
  have he : Nat.pair 1 (Nat.unpair a).2 = a := by rw [← ht]; exact Nat.pair_unpair a
  refine ⟨by simpa [product, support] using And.intro hn hT, ?_, ?_⟩ <;>
    exact ⟨a, by simpa using ha, a, by simp [inrRepresentative, he], hs⟩

def decompositionRepresentative (f : Representative R (coproduct S T)) :
    Representative R (coproduct (pullbackPER f (inlRepresentative S T))
      (pullbackPER f (inrRepresentative S T))) where
  val n := (f.val n).map (decompositionCode n)
  computable := f.computable.map (Primrec₂.natPair.to_comp.comp
    (Computable.fst.comp (Computable.unpair.comp Computable.snd))
    (Primrec₂.natPair.to_comp.comp Computable.fst
      (Computable.snd.comp (Computable.unpair.comp Computable.snd)))).to₂
  total := fun n hn ↦ f.total n hn
  respects := by
    intro n m a b hnm ha hb
    obtain ⟨x, hx, rfl⟩ := (Part.mem_map_iff _).mp ha
    obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp hb
    have hxy := f.respects hnm hx hy
    simp only [coproduct, decompositionCode, Nat.unpair_pair]
    rcases hxy with ⟨hx0, hy0, hS⟩ | ⟨hx1, hy1, hT⟩
    · exact Or.inl ⟨hx0, hy0, ⟨by simpa [product, support] using And.intro hnm hS,
        (pullback_inl_supported f (supported_left hnm) hx hx0).2.1,
        (pullback_inl_supported f (supported_right hnm) hy hy0).2.1⟩⟩
    · exact Or.inr ⟨hx1, hy1, ⟨by simpa [product, support] using And.intro hnm hT,
        (pullback_inr_supported f (supported_left hnm) hx hx1).2.1,
        (pullback_inr_supported f (supported_right hnm) hy hy1).2.1⟩⟩

def decompositionComparison (f : Representative R (coproduct S T)) :
    coproduct (pullbackPER f (inlRepresentative S T))
      (pullbackPER f (inrRepresentative S T)) ⟶ R :=
  copair (pullbackFst f (inlRepresentative S T)) (pullbackFst f (inrRepresentative S T))

@[simp] theorem decomposition_inv_hom (f : Representative R (coproduct S T)) :
    ofRepresentative (decompositionRepresentative f) ≫ decompositionComparison f = 𝟙 R := by
  apply Quotient.sound
  intro n hn a ha b hb
  obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
  obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp hx
  have ha' : a = n := by
    simpa [copairRepresentative, pullbackFstRepresentative, decompositionCode] using ha
  have hb' : b = n := Part.mem_some_iff.mp hb
  simpa [ha', hb', support] using hn

theorem decomposition_related (f : Representative R (coproduct S T))
    {n a : ℕ}
    (hn : n ∈ (coproduct (pullbackPER f (inlRepresentative S T))
      (pullbackPER f (inrRepresentative S T))).support)
    (ha : a ∈ f.val (Nat.unpair (Nat.unpair n).2).1) :
    (coproduct (pullbackPER f (inlRepresentative S T))
      (pullbackPER f (inrRepresentative S T))).rel
      (decompositionCode (Nat.unpair (Nat.unpair n).2).1 a) n := by
  rcases hn with ⟨hn0, _, hL⟩ | ⟨hn1, _, hR⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hL.2.1
    have hxa : x = a := Part.mem_unique hx ha
    have hy' : y = Nat.pair 0 (Nat.unpair (Nat.unpair n).2).2 := Part.mem_some_iff.mp hy
    rw [hxa, hy'] at hxy
    have hh : (Nat.unpair a).1 = 0 ∧
        S.rel (Nat.unpair a).2 (Nat.unpair (Nat.unpair n).2).2 := by
      simpa [coproduct] using hxy
    simp only [coproduct, decompositionCode, Nat.unpair_pair]
    exact Or.inl ⟨hh.1, hn0, ⟨by simpa [product, support] using And.intro hL.1.1 hh.2,
      (pullback_inl_supported f hL.1.1 ha hh.1).2.1, hL.2.1⟩⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hR.2.1
    have hxa : x = a := Part.mem_unique hx ha
    have hy' : y = Nat.pair 1 (Nat.unpair (Nat.unpair n).2).2 := Part.mem_some_iff.mp hy
    rw [hxa, hy'] at hxy
    have hh : (Nat.unpair a).1 = 1 ∧
        T.rel (Nat.unpair a).2 (Nat.unpair (Nat.unpair n).2).2 := by
      simpa [coproduct] using hxy
    simp only [coproduct, decompositionCode, Nat.unpair_pair]
    exact Or.inr ⟨hh.1, hn1, ⟨by simpa [product, support] using And.intro hR.1.1 hh.2,
      (pullback_inr_supported f hR.1.1 ha hh.1).2.1, hR.2.1⟩⟩

@[simp] theorem decomposition_hom_inv (f : Representative R (coproduct S T)) :
    decompositionComparison f ≫ ofRepresentative (decompositionRepresentative f) = 𝟙 _ := by
  apply Quotient.sound
  intro n hn a ha b hb
  obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
  have hx' : x = (Nat.unpair (Nat.unpair n).2).1 := by
    simpa [copairRepresentative, pullbackFstRepresentative] using hx
  obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp ha
  have hb' : b = n := Part.mem_some_iff.mp hb
  rw [hx', hb']
  exact decomposition_related f hn (hx' ▸ hy)

def decompositionIso (f : Representative R (coproduct S T)) :
    coproduct (pullbackPER f (inlRepresentative S T))
      (pullbackPER f (inrRepresentative S T)) ≅ R where
  hom := decompositionComparison f
  inv := ofRepresentative (decompositionRepresentative f)
  hom_inv_id := decomposition_hom_inv f
  inv_hom_id := decomposition_inv_hom f

/-- The two inverse images of coproduct summands form a coproduct of the source. -/
def pullbackCoproductIsColimit (f : Representative R (coproduct S T)) :
    IsColimit (BinaryCofan.mk (pullbackFst f (inlRepresentative S T))
      (pullbackFst f (inrRepresentative S T))) :=
  IsColimit.ofIsoColimit (coproductIsColimit _ _)
    (BinaryCofan.ext (decompositionIso f) (by simp [decompositionIso, decompositionComparison])
      (by simp [decompositionIso, decompositionComparison]))

/-- The decomposition for Mathlib's chosen pullbacks and an arbitrary morphism. -/
def chosenPullbackCoproductIsColimit (f : R ⟶ coproduct S T) :
    IsColimit (BinaryCofan.mk (pullback.fst f (inl S T)) (pullback.fst f (inr S T))) := by
  apply Classical.choice
  induction f using Quotient.inductionOn with | _ f =>
    let eL := (pullback_isPullback f (inlRepresentative S T)).isoPullback
    let eR := (pullback_isPullback f (inrRepresentative S T)).isoPullback
    have hL := (BinaryCofan.mk (pullbackFst f (inlRepresentative S T))
      (pullbackFst f (inrRepresentative S T))).isColimitCompLeftIso eL.inv
        (pullbackCoproductIsColimit f)
    have hLR := (BinaryCofan.mk (eL.inv ≫ pullbackFst f (inlRepresentative S T))
      (pullbackFst f (inrRepresentative S T))).isColimitCompRightIso eR.inv hL
    simp only [BinaryCofan.mk_inl, BinaryCofan.mk_inr, eL, eR,
      IsPullback.isoPullback_inv_fst, pair_obj_left] at hLR
    exact ⟨by simpa only [inl, inr, ofRepresentative] using hLR⟩

end NumericalPER
end CategoricalEssentialIncompleteness
