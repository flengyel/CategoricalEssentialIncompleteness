/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.PCat

/-!
# `P`-recursion categories

`P`-recursion categories: Appendix A, section A.6.

Zero morphisms come from Mathlib's `Limits.HasZeroMorphisms` rather than a local
redefinition. `Prodominical` is a Prop-valued mixin, `PRecursionCategory` takes
the whole ambient structure as instance parameters, so no `extends` chain has to
be resolved.
-/

@[expose] public section

universe v u

namespace CategoryTheory

/-! ## 3. `P`-recursion categories (Appendix A, §A.6) -/

namespace RecursionCategory

open PCategoryStruct

/-- Prodominical: zero morphisms are absorbed by the near product.  Uses
Mathlib's `Limits.HasZeroMorphisms` rather than a local redefinition. -/
class Prodominical (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] : Prop where
  nearProd_zero_right : ∀ {A B X Y : C} (f : A ⟶ B),
    nearProd_map f (0 : X ⟶ Y) = (0 : nearProd A X ⟶ nearProd B Y)
  nearProd_zero_left : ∀ {A B X Y : C} (f : A ⟶ B),
    nearProd_map (0 : X ⟶ Y) f = (0 : nearProd X A ⟶ nearProd Y B)

/-- Isotype: any two objects are isomorphic.  Stated as a `Prop` (the appendix
asserts existence, not a chosen family of isomorphisms). -/
class Isotype (C : Type u) [Category.{v} C] : Prop where
  iso : ∀ (X Y : C), Nonempty (X ≅ Y)

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- Turing morphism: every `φ : V ⊠ X ⟶ Y` factors through `τ` along a total
`g : V ⟶ W`. -/
def IsTuringMorphism {W X Y : C} (τ : nearProd W X ⟶ Y) : Prop :=
  ∀ (V : C) (φ : nearProd V X ⟶ Y),
    ∃ g : V ⟶ W, RestrictionCategory.isTotal g ∧ nearProd_map g (𝟙 X) ≫ τ = φ

/-- A `P`-recursion category is a prodominical isotype equipped with a Turing
morphism.  The ambient structure enters as instance parameters, so no `extends`
chain has to be resolved. -/
class PRecursionCategory (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [PCategory C] [Limits.HasZeroMorphisms C] [Prodominical C] [Isotype C] where
  W : C
  X : C
  Y : C
  tau : nearProd W X ⟶ Y
  is_turing : IsTuringMorphism tau

end RecursionCategory
end CategoryTheory
