/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkProducts

/-! # Component images commute with restriction products -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EnumerableCarriers

theorem mem_val_range {X Y : Carrier} (f : X ⟶ Y) (x y : ℕ) :
    y ∈ val (Ranges.range f).hom x ↔ (∃ z,x ∈ val f z) ∧ y=x := by
  rw [mem_val_idem,support_range]
  rfl

theorem range_product {W X Y Z : Carrier} (f : W ⟶ X) (g : Y ⟶ Z) :
    (Ranges.range (partialProdMap f g)).hom=
      partialProdMap (Ranges.range f).hom (Ranges.range g).hom := by
  apply val_injective
  apply PFun.ext
  intro n m
  rw [mem_val_range,mem_partialProdMap_iff]
  simp only [mem_val_range]
  constructor
  · rintro ⟨⟨z,hz⟩,he⟩
    subst m
    obtain ⟨hf,hg⟩ := (mem_partialProdMap_iff f g z n).mp hz
    exact ⟨⟨⟨(Nat.unpair z).1,hf⟩,rfl⟩,⟨⟨(Nat.unpair z).2,hg⟩,rfl⟩⟩
  · rintro ⟨⟨⟨x,hx⟩,he0⟩,⟨⟨y,hy⟩,he1⟩⟩
    have hm : m=n := by
      calc m=Nat.pair (Nat.unpair m).1 (Nat.unpair m).2 := (Nat.pair_unpair m).symm
           _=Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 := congrArg₂ Nat.pair he0 he1
           _=n := Nat.pair_unpair n
    refine ⟨⟨Nat.pair x y,(mem_partialProdMap_iff f g _ _).mpr ?_⟩,hm⟩
    simpa only [Nat.unpair_pair] using And.intro hx hy

end EnumerableCarriers

namespace EffectiveFork

theorem range_product {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) :
    (Ranges.range (productMap f g)).hom=
      productMap (Ranges.range f).hom (Ranges.range g).hom :=
  Hom.ext (EnumerableCarriers.range_product f.center g.center)
    (EnumerableCarriers.range_product f.left g.left)
    (EnumerableCarriers.range_product f.right g.right)

end EffectiveFork
end CategoricalEssentialIncompleteness.LocalConnectedness
