/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerablePCategory

/-! # Associative programs give associative internal multiplications -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

theorem associative_of_values {M : Carrier} (mu : product M M ⟶ M) (m : ℕ → ℕ → ℕ)
    (hm : ∀ a ∈ M.support,∀ b ∈ M.support,val mu (Nat.pair a b)=Part.some (m a b))
    (ha : ∀ a ∈ M.support,∀ b ∈ M.support,∀ c ∈ M.support,m (m a b) c=m a (m b c)) :
    partialProdMap mu (𝟙 M) ≫ mu=
      PCategoryStruct.assoc M M M ≫ partialProdMap (𝟙 M) mu ≫ mu := by
  apply val_ext_on_source
  intro n hn
  let a := (Nat.unpair (Nat.unpair n).1).1
  let b := (Nat.unpair (Nat.unpair n).1).2
  let c := (Nat.unpair n).2
  have hA : a ∈ M.support := hn.1.1
  have hB : b ∈ M.support := hn.1.2
  have hC : c ∈ M.support := hn.2
  have hn' : Nat.pair (Nat.pair a b) c=n := by simp only [a,b,c,Nat.pair_unpair]
  have hmul (a b : ℕ) (hA : a ∈ M.support) (hB : b ∈ M.support) :
      m a b ∈ val mu (Nat.pair a b) := Part.eq_some_iff.mp (hm a hA b hB)
  have hAB := val_target mu _ _ (hmul a b hA hB)
  have hBC := val_target mu _ _ (hmul b c hB hC)
  have hp : val (partialProdMap mu (𝟙 M)) n=Part.some (Nat.pair (m a b) c) := by
    apply Part.eq_some_iff.mpr
    apply (mem_partialProdMap_iff _ _ _ _).mpr
    rw [← hn']
    simpa only [val_id,Nat.unpair_pair] using
      And.intro (hmul a b hA hB) ((mem_supportIdentity _ _ _).mpr ⟨hC,rfl⟩)
  have hq : val (PCategoryStruct.assoc M M M) n=Part.some (Nat.pair a (Nat.pair b c)) :=
    Part.eq_some_iff.mpr ((mem_pcategory_assoc _ _ _ _ _).mpr ⟨hn,rfl⟩)
  have hr : val (partialProdMap (𝟙 M) mu) (Nat.pair a (Nat.pair b c))=
      Part.some (Nat.pair a (m b c)) := by
    apply Part.eq_some_iff.mpr
    apply (mem_partialProdMap_iff _ _ _ _).mpr
    simp only [Nat.unpair_pair]
    simpa only [val_id] using
      And.intro ((mem_supportIdentity _ _ _).mpr ⟨hA,rfl⟩) (hmul b c hB hC)
  simp only [val_comp,hp,hq,hr,Part.bind_some,hm (m a b) hAB c hC,
    hm a hA (m b c) hBC,ha a hA b hB c hC]

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
