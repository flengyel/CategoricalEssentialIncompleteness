/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceFinitePowers

/-! # Independent checks of ordered relative premise tuples -/
@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] {P : D}
local instance : Regular (Over P) := RegularSlices.regular P
variable {X F G : Over P} (q : F ⟶ G) (n : ℕ)

example (f : X.left ⟶ finitePower F.left n) (k : X ⟶ finitePower G n)
    (h : f ≫ finitePowerMap q.left n = k.left ≫ SliceFinitePowers.comparison G n) :
    ∃ lift : X ⟶ finitePower F n,
      lift.left ≫ SliceFinitePowers.comparison F n = f ∧ lift ≫ finitePowerMap q n = k :=
  ⟨SliceFinitePowers.lift q n f k h, SliceFinitePowers.lift_value q n f k h,
    SliceFinitePowers.lift_map q n f k h⟩

example (f g : X ⟶ finitePower F n)
    (h : f.left ≫ SliceFinitePowers.comparison F n = g.left ≫ SliceFinitePowers.comparison F n) :
    f = g := SliceFinitePowers.hom_ext n f g h

example : (finitePower F 0).left ⟶ ⊤_ D := SliceFinitePowers.comparison F 0
example : SliceFinitePowers.comparison F 1 = 𝟙 F.left := rfl

#print axioms SliceFinitePowers.naturality
#print axioms SliceFinitePowers.hom_ext
#print axioms SliceFinitePowers.lift
#print axioms SliceFinitePowers.lift_value
#print axioms SliceFinitePowers.lift_map
