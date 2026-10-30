/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkUniversal

/-! # Total fork morphisms constructed from recursive component functions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EnumerableCarriers

theorem totalFromFunction_comp {X Y Z : Carrier} (f g : ℕ → ℕ)
    (hf : Computable f) (hg : Computable g)
    (hs : ∀ x ∈ X.support, f x ∈ Y.support)
    (ht : ∀ y ∈ Y.support, g y ∈ Z.support) :
    totalFromFunction f hf hs ≫ totalFromFunction g hg ht =
      totalFromFunction (g ∘ f) (hg.comp hf) (fun x hx => ht (f x) (hs x hx)) := by
  apply val_injective
  apply PFun.ext
  intro x z
  simp only [mem_val_comp,mem_totalFromFunction,Function.comp_apply]
  constructor
  · rintro ⟨y,⟨hx,rfl⟩,_,hz⟩
    exact ⟨hx,hz⟩
  · rintro ⟨hx,hz⟩
    exact ⟨f x,⟨hx,rfl⟩,hs x hx,hz⟩

theorem totalFromFunction_eq_id {X : Carrier} (f : ℕ → ℕ) (hf : Computable f)
    (hs : ∀ x ∈ X.support, f x ∈ X.support) (he : ∀ x ∈ X.support,f x=x) :
    totalFromFunction f hf hs=𝟙 X := by
  apply val_injective
  apply PFun.ext
  intro x y
  change y ∈ val (totalFromFunction f hf hs) x ↔ y ∈ val (⊤ : Idem X).hom x
  rw [mem_totalFromFunction,mem_val_idem,support_top]
  exact and_congr_right (fun hx => by rw [he x hx])

theorem totalFromFunction_inverse {X Y : Carrier} (f g : ℕ → ℕ)
    (hf : Computable f) (hg : Computable g)
    (hs : ∀ x ∈ X.support,f x ∈ Y.support)
    (ht : ∀ x ∈ Y.support,g x ∈ X.support)
    (he : ∀ x ∈ X.support,g (f x)=x) :
    totalFromFunction f hf hs ≫ totalFromFunction g hg ht=𝟙 X :=
  (totalFromFunction_comp f g hf hg hs ht).trans
    (totalFromFunction_eq_id _ (hg.comp hf) (fun x hx => ht _ (hs x hx)) he)

end EnumerableCarriers

namespace EffectiveFork

open EnumerableCarriers (Carrier val totalFromFunction)

@[simp] theorem comp_center {X Y Z : Object} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).center=f.center ≫ g.center := rfl
@[simp] theorem comp_left {X Y Z : Object} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left=f.left ≫ g.left := rfl
@[simp] theorem comp_right {X Y Z : Object} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right=f.right ≫ g.right := rfl
@[simp] theorem id_center (X : Object) : (𝟙 X : X ⟶ X).center=𝟙 X.center := rfl
@[simp] theorem id_left (X : Object) : (𝟙 X : X ⟶ X).left=𝟙 X.left := rfl
@[simp] theorem id_right (X : Object) : (𝟙 X : X ⟶ X).right=𝟙 X.right := rfl

def computedMap {X Y : Object} (f0 f1 f2 : ℕ → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2)
    (s0 : ∀ x ∈ X.center.support,f0 x ∈ Y.center.support)
    (s1 : ∀ x ∈ X.left.support,f1 x ∈ Y.left.support)
    (s2 : ∀ x ∈ X.right.support,f2 x ∈ Y.right.support)
    (n1 : ∀ x u, u ∈ val X.leftMap x → f1 u ∈ val Y.leftMap (f0 x))
    (n2 : ∀ x u, u ∈ val X.rightMap x → f2 u ∈ val Y.rightMap (f0 x)) : X ⟶ Y where
  center := totalFromFunction f0 h0 s0
  left := totalFromFunction f1 h1 s1
  right := totalFromFunction f2 h2 s2
  natural_left := by
    intro x y u v hxy hxu hyv
    obtain ⟨_,rfl⟩ := (EnumerableCarriers.mem_totalFromFunction _ _ _ x y).mp hxy
    exact (EnumerableCarriers.mem_totalFromFunction _ _ _ u v).mpr
      ⟨EnumerableCarriers.val_target X.leftMap x u hxu,Part.mem_unique hyv (n1 x u hxu)⟩
  natural_right := by
    intro x y u v hxy hxu hyv
    obtain ⟨_,rfl⟩ := (EnumerableCarriers.mem_totalFromFunction _ _ _ x y).mp hxy
    exact (EnumerableCarriers.mem_totalFromFunction _ _ _ u v).mpr
      ⟨EnumerableCarriers.val_target X.rightMap x u hxu,Part.mem_unique hyv (n2 x u hxu)⟩

theorem computedMap_total {X Y : Object} (f0 f1 f2 : ℕ → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2)
    (s0 : ∀ x ∈ X.center.support,f0 x ∈ Y.center.support)
    (s1 : ∀ x ∈ X.left.support,f1 x ∈ Y.left.support)
    (s2 : ∀ x ∈ X.right.support,f2 x ∈ Y.right.support)
    (n1 : ∀ x u, u ∈ val X.leftMap x → f1 u ∈ val Y.leftMap (f0 x))
    (n2 : ∀ x u, u ∈ val X.rightMap x → f2 u ∈ val Y.rightMap (f0 x)) :
    isTotal (computedMap f0 f1 f2 h0 h1 h2 s0 s1 s2 n1 n2) :=
  (total_iff _).mpr ⟨EnumerableCarriers.totalFromFunction_total f0 h0 s0,
    EnumerableCarriers.totalFromFunction_total f1 h1 s1,
    EnumerableCarriers.totalFromFunction_total f2 h2 s2⟩

end EffectiveFork
end CategoricalEssentialIncompleteness.LocalConnectedness
