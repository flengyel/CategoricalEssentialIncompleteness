/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkFunctions
public import CategoricalEssentialIncompleteness.EnumerableWords

/-! # Letterwise nonempty words on effective forks -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

theorem respects_lists {C A D B : Carrier} {r : C ⟶ A} {s : D ⟶ B}
    {f : C ⟶ D} {g : A ⟶ B} (h : Respects r s f g)
    {xs ys us vs : List ℕ}
    (hxy : List.Forall₂ (fun x y => y ∈ val f x) xs ys)
    (hxu : List.Forall₂ (fun x u => u ∈ val r x) xs us)
    (hyv : List.Forall₂ (fun y v => v ∈ val s y) ys vs) :
    List.Forall₂ (fun u v => v ∈ val g u) us vs := by
  induction hxy generalizing us vs with
  | nil => cases hxu; cases hyv; exact List.Forall₂.nil
  | @cons x y xs ys hxy hxs ih =>
    cases hxu with
    | cons hxu hus =>
      cases hyv with
      | cons hyv hvs => exact List.Forall₂.cons (h _ _ _ _ hxy hxu hyv) (ih hus hvs)

theorem respects_words {C A D B : Carrier} {r : C ⟶ A} {s : D ⟶ B}
    {f : C ⟶ D} {g : A ⟶ B} (h : Respects r s f g) :
    Respects (EnumerableCarriers.wordMap r) (EnumerableCarriers.wordMap s)
      (EnumerableCarriers.wordMap f) (EnumerableCarriers.wordMap g) := by
  intro x y u v hxy hxu hyv
  rw [EnumerableCarriers.mem_wordMap] at hxy hxu hyv ⊢
  exact respects_lists h hxy hxu hyv

def words (X : Object) : Object where
  center := EnumerableCarriers.words X.center
  left := EnumerableCarriers.words X.left
  right := EnumerableCarriers.words X.right
  leftMap := EnumerableCarriers.wordMap X.leftMap
  rightMap := EnumerableCarriers.wordMap X.rightMap
  left_total := EnumerableCarriers.wordMap_total X.leftMap X.left_total
  right_total := EnumerableCarriers.wordMap_total X.rightMap X.right_total

def wordMap {X Y : Object} (f : X ⟶ Y) : words X ⟶ words Y :=
  ⟨EnumerableCarriers.wordMap f.center,EnumerableCarriers.wordMap f.left,
    EnumerableCarriers.wordMap f.right,respects_words f.natural_left,respects_words f.natural_right⟩

theorem wordMap_total {X Y : Object} (f : X ⟶ Y) (hf : isTotal f) : isTotal (wordMap f) :=
  (total_iff _).mpr ⟨EnumerableCarriers.wordMap_total f.center ((total_iff f).mp hf).1,
    EnumerableCarriers.wordMap_total f.left ((total_iff f).mp hf).2.1,
    EnumerableCarriers.wordMap_total f.right ((total_iff f).mp hf).2.2⟩

theorem wordMap_id (X : Object) : wordMap (𝟙 X)=𝟙 (words X) :=
  Hom.ext (EnumerableCarriers.wordMap_id X.center) (EnumerableCarriers.wordMap_id X.left)
    (EnumerableCarriers.wordMap_id X.right)

theorem wordMap_comp {X Y Z : Object} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wordMap (f ≫ g)=wordMap f ≫ wordMap g :=
  Hom.ext (EnumerableCarriers.wordMap_comp f.center g.center)
    (EnumerableCarriers.wordMap_comp f.left g.left) (EnumerableCarriers.wordMap_comp f.right g.right)

def wordFunctor : Object ⥤ Object where
  obj := words
  map := wordMap
  map_id := wordMap_id
  map_comp := wordMap_comp

def wordIso {X Y : Object} (i : X ≅ Y) : words X ≅ words Y := wordFunctor.mapIso i

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
