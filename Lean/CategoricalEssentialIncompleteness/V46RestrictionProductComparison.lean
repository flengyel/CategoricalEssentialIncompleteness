/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionProductData

/-! # Canonical comparison of restriction-product choices -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.RestrictionProducts

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

structure BinaryProduct (X Y : C) where
  obj : C
  fst : obj ⟶ X
  snd : obj ⟶ Y
  pair : ∀ {V}, (V ⟶ X) → (V ⟶ Y) → (V ⟶ obj)
  fst_total : isTotal fst
  snd_total : isTotal snd
  pair_fst : ∀ {V} (f : V ⟶ X) (g : V ⟶ Y), pair f g ≫ fst = rst g ≫ f
  pair_snd : ∀ {V} (f : V ⟶ X) (g : V ⟶ Y), pair f g ≫ snd = rst f ≫ g
  pair_restriction : ∀ {V} (f : V ⟶ X) (g : V ⟶ Y), rst (pair f g) = rst f ≫ rst g
  pair_proj : ∀ {V} (h : V ⟶ obj), pair (h ≫ fst) (h ≫ snd) = h

namespace BinaryProduct

variable {X Y : C} (P Q : BinaryProduct X Y)

theorem hom_ext {V : C} {h k : V ⟶ P.obj}
    (h0 : h ≫ P.fst = k ≫ P.fst) (h1 : h ≫ P.snd = k ≫ P.snd) : h = k := by
  rw [← P.pair_proj h, ← P.pair_proj k, h0, h1]

def comparison : P.obj ⟶ Q.obj := Q.pair P.fst P.snd

theorem comparison_fst : P.comparison Q ≫ Q.fst = P.fst := by
  change Q.pair P.fst P.snd ≫ Q.fst = P.fst
  rw [Q.pair_fst, P.snd_total, Category.id_comp]

theorem comparison_snd : P.comparison Q ≫ Q.snd = P.snd := by
  change Q.pair P.fst P.snd ≫ Q.snd = P.snd
  rw [Q.pair_snd, P.fst_total, Category.id_comp]

theorem comparison_total : isTotal (P.comparison Q) := by
  change rst (Q.pair P.fst P.snd) = 𝟙 P.obj
  rw [Q.pair_restriction, P.fst_total, P.snd_total, Category.id_comp]

def iso : P.obj ≅ Q.obj where
  hom := P.comparison Q
  inv := Q.comparison P
  hom_inv_id := by
    apply P.hom_ext
    · rw [Category.assoc, Q.comparison_fst P, P.comparison_fst Q, Category.id_comp]
    · rw [Category.assoc, Q.comparison_snd P, P.comparison_snd Q, Category.id_comp]
  inv_hom_id := by
    apply Q.hom_ext
    · rw [Category.assoc, P.comparison_fst Q, Q.comparison_fst P, Category.id_comp]
    · rw [Category.assoc, P.comparison_snd Q, Q.comparison_snd P, Category.id_comp]

end BinaryProduct

def ProductData.binary (D : ProductData C) (X Y : C) : BinaryProduct X Y where
  obj := D.prod X Y
  fst := D.fst X Y
  snd := D.snd X Y
  pair := D.pair
  fst_total := D.fst_total X Y
  snd_total := D.snd_total X Y
  pair_fst := D.pair_fst
  pair_snd := D.pair_snd
  pair_restriction := D.pair_restriction
  pair_proj := D.pair_proj

end CategoricalEssentialIncompleteness.V46.RestrictionProducts
