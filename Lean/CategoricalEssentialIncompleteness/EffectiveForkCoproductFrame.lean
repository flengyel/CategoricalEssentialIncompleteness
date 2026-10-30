/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkFunctions

/-! # The parity coproduct frame on the universal fork -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def tagSplit (x : ℕ) : ℕ :=
  2*Nat.pair ((Nat.unpair x).1/2) (Nat.unpair x).2+(Nat.unpair x).1%2

def tagMerge (x : ℕ) : ℕ :=
  Nat.pair (2*(Nat.unpair (x/2)).1+x%2) (Nat.unpair (x/2)).2

theorem tagSplit_computable : Computable tagSplit := by
  have k := Computable.fst.comp Computable.unpair
  have d := Primrec.nat_div.to_comp.comp k (.const 2)
  have m := Primrec.nat_mod.to_comp.comp k (.const 2)
  exact Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (.const 2)
      (Primrec₂.natPair.to_comp.comp d (Computable.snd.comp .unpair))) m

theorem tagMerge_computable : Computable tagMerge := by
  have d := Primrec.nat_div.to_comp.comp Computable.id (.const 2)
  have m := Primrec.nat_mod.to_comp.comp Computable.id (.const 2)
  have k := Computable.fst.comp (Computable.unpair.comp d)
  exact Primrec₂.natPair.to_comp.comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 2) k) m)
    (Computable.snd.comp (Computable.unpair.comp d))

private theorem two_div_mod (n : ℕ) : 2*(n/2)+n%2=n := by omega

@[simp] theorem merge_split_tag (x : ℕ) : tagMerge (tagSplit x)=x := by
  have hm : (Nat.unpair x).1%2<2 := Nat.mod_lt _ (by omega)
  simp [tagMerge,tagSplit,Nat.add_div,Nat.add_mod,Nat.mod_eq_of_lt hm,Nat.not_le.mpr hm,two_div_mod,
    Nat.pair_unpair]

@[simp] theorem split_merge_tag (x : ℕ) : tagSplit (tagMerge x)=x := by
  have hm : x%2<2 := Nat.mod_lt _ (by omega)
  simp [tagMerge,tagSplit,Nat.add_div,Nat.add_mod,Nat.mod_eq_of_lt hm,Nat.not_le.mpr hm,two_div_mod,
    Nat.pair_unpair]

private theorem sum_support (x : ℕ) :
    x ∈ (EnumerableCarriers.coproduct natCarrier natCarrier).support := by
  by_cases he : x%2=0
  · exact Or.inl ⟨he,Set.mem_univ _⟩
  · exact Or.inr ⟨by omega,Set.mem_univ _⟩

theorem tagSplit_respects (r : ℕ → ℕ) (hr : Computable r)
    (hk : ∀ k x, (Nat.unpair (r (Nat.pair k x))).1=k)
    (ht : ∀ k q x, (Nat.unpair (r (Nat.pair k x))).2=
      (Nat.unpair (r (Nat.pair q x))).2) (x : ℕ) :
    tagSplit (r x) ∈ val
      (CategoryTheory.CoprodStruct.coprod_map
        (EnumerableCarriers.totalFromFunction (X := natCarrier) (Y := natCarrier)
          r hr (fun _ _ => Set.mem_univ _))
        (EnumerableCarriers.totalFromFunction (X := natCarrier) (Y := natCarrier)
          r hr (fun _ _ => Set.mem_univ _))) (tagSplit x) := by
  have hx : x=Nat.pair (Nat.unpair x).1 (Nat.unpair x).2 := (Nat.pair_unpair x).symm
  have he : tagSplit (r x)=
      2*r (Nat.pair ((Nat.unpair x).1/2) (Nat.unpair x).2)+(Nat.unpair x).1%2 := by
    conv_lhs => rw [hx]
    simp only [tagSplit,hk,Nat.unpair_pair]
    rw [ht (Nat.unpair x).1 ((Nat.unpair x).1/2)]
    have hp := Nat.pair_unpair (r (Nat.pair ((Nat.unpair x).1/2) (Nat.unpair x).2))
    rw [hk] at hp
    exact congrArg (fun n => 2*n+(Nat.unpair x).1%2) hp
  rw [he]
  by_cases hm : (Nat.unpair x).1%2=0
  · simp only [tagSplit,hm,Nat.add_zero,EnumerableCarriers.val_map_even]
    exact (Part.mem_map_iff _).mpr ⟨r _,
      (EnumerableCarriers.mem_totalFromFunction _ hr (fun _ _ => Set.mem_univ _) _ _).mpr
        ⟨Set.mem_univ _,rfl⟩,rfl⟩
  · have hm' : (Nat.unpair x).1%2=1 := by omega
    simp only [tagSplit,hm',EnumerableCarriers.val_map_odd]
    exact (Part.mem_map_iff _).mpr ⟨r _,
      (EnumerableCarriers.mem_totalFromFunction _ hr (fun _ _ => Set.mem_univ _) _ _).mpr
        ⟨Set.mem_univ _,rfl⟩,rfl⟩

def coproductFrameForward : V ⟶ coproduct V V :=
  computedMap tagSplit tagSplit tagSplit tagSplit_computable tagSplit_computable
    tagSplit_computable (fun _ _ => sum_support _) (fun _ _ => sum_support _)
    (fun _ _ => sum_support _)
    (by
      intro x u hu
      rw [(mem_V_left x u).mp hu]
      exact tagSplit_respects leftCoordinate leftCoordinate_computable
        (by intros; simp [leftCoordinate]) (by intros; simp [leftCoordinate]) x)
    (by
      intro x u hu
      rw [(mem_V_right x u).mp hu]
      exact tagSplit_respects rightCoordinate rightCoordinate_computable
        (by intros; simp [rightCoordinate]) (by intros; simp [rightCoordinate]) x)

/-- The inverse is natural because the forward component maps are injective,
and their inverses have exactly the reversed graphs. -/
def coproductFrameBackward : coproduct V V ⟶ V :=
  let f := coproductFrameForward
  let inv := EnumerableCarriers.totalFromFunction (X := EnumerableCarriers.coproduct natCarrier natCarrier)
    (Y := natCarrier) tagMerge tagMerge_computable (fun _ _ => Set.mem_univ _)
  let reverse : ∀ y x, x ∈ val inv y ↔ y ∈ val f.center x := by
    intro y x
    change x ∈ val (EnumerableCarriers.totalFromFunction tagMerge tagMerge_computable
      (fun _ _ => Set.mem_univ _)) y ↔
      y ∈ val (EnumerableCarriers.totalFromFunction tagSplit tagSplit_computable
        (fun _ _ => sum_support _)) x
    simp only [EnumerableCarriers.mem_totalFromFunction]
    constructor
    · rintro ⟨_,rfl⟩
      exact ⟨Set.mem_univ _,(split_merge_tag y).symm⟩
    · rintro ⟨_,rfl⟩
      exact ⟨sum_support _,(merge_split_tag x).symm⟩
  ⟨inv,inv,inv,respects_inverse f.natural_left inv inv reverse reverse,
    respects_inverse f.natural_right inv inv reverse reverse⟩

def coproductFrame : V ≅ coproduct V V where
  hom := coproductFrameForward
  inv := coproductFrameBackward
  hom_inv_id := by
    apply Hom.ext
    all_goals
      simp only [comp_center,comp_left,comp_right,id_center,id_left,id_right]
      dsimp only [coproductFrameForward,coproductFrameBackward,computedMap]
      rw [EnumerableCarriers.totalFromFunction_comp]
      apply EnumerableCarriers.totalFromFunction_eq_id
      intro x hx
      exact merge_split_tag x
  inv_hom_id := by
    apply Hom.ext
    all_goals
      simp only [comp_center,comp_left,comp_right,id_center,id_left,id_right]
      dsimp only [coproductFrameForward,coproductFrameBackward,computedMap]
      rw [EnumerableCarriers.totalFromFunction_comp]
      apply EnumerableCarriers.totalFromFunction_eq_id
      intro x hx
      exact split_merge_tag x

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
