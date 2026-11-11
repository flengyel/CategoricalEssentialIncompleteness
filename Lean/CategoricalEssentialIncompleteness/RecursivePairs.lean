/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalRealization

/-! # Disjoint c.e. pairs and total recursive pair morphisms -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.RecursivePairs

open ClassicalPrograms (Rec)

structure Object where
  carrier : Rec
  positive : Idem carrier
  negative : Idem carrier
  disjoint : positive ⊓ negative=⊥

structure Hom (X Y : Object) where
  map : X.carrier ⟶ Y.carrier
  total : isTotal map
  positive : X.positive ≤ Idem.pull map Y.positive
  negative : X.negative ≤ Idem.pull map Y.negative

@[ext] theorem Hom.ext {X Y : Object} {f g : Hom X Y} (h : f.map=g.map) : f=g := by
  cases f
  cases g
  cases h
  rfl

def identity (X : Object) : Hom X X where
  map := 𝟙 X.carrier
  total := rst_id _
  positive := by rw [Idem.pull_id]
  negative := by rw [Idem.pull_id]

def composition {X Y Z : Object} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  map := f.map ≫ g.map
  total := isTotal_comp f.total g.total
  positive := by
    rw [Idem.pull_comp]
    exact f.positive.trans (Idem.pull_mono f.map g.positive)
  negative := by
    rw [Idem.pull_comp]
    exact f.negative.trans (Idem.pull_mono f.map g.negative)

instance : Category Object where
  Hom := Hom
  id := identity
  comp := composition
  id_comp f := Hom.ext (Category.id_comp f.map)
  comp_id f := Hom.ext (Category.comp_id f.map)
  assoc f g h := Hom.ext (Category.assoc f.map g.map h.map)

theorem supportIdems_disjoint (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hd : Disjoint A B) :
    ClassicalPrograms.supportIdem A hA ⊓ ClassicalPrograms.supportIdem B hB=⊥ := by
  apply Idem.ext
  apply ClassicalPrograms.J.map_injective
  change ClassicalPrograms.J.map ((ClassicalPrograms.supportIdem A hA).hom ≫
    (ClassicalPrograms.supportIdem B hB).hom)=ClassicalPrograms.J.map 0
  rw [ClassicalPrograms.J.map_comp]
  change (fun x : ℕ => (supportIdentity A x).bind (supportIdentity B))=
    (fun _ : ℕ => Part.none)
  apply PFun.ext
  intro x y
  change y ∈ (supportIdentity A x).bind (supportIdentity B) ↔ y ∈ Part.none
  simp only [Part.mem_bind_iff,mem_supportIdentity,Part.notMem_none,iff_false]
  rintro ⟨z,⟨ha,he⟩,hb,_⟩
  subst z
  exact Set.disjoint_left.mp hd ha hb

end CategoricalEssentialIncompleteness.LocalConnectedness.RecursivePairs
