/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SliceProductCoordinates

/-! # Statement checks for products and constant families in a slice -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46


variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] {P X : D}
variable {W A B : Over P}

example (f : W ⟶ A) (g : W ⟶ B) :
    (prod.lift f g).left ≫ (prod.fst : A ⨯ B ⟶ A).left = f.left :=
  SliceProductCoordinates.lift_fst f g
example {f g : W ⟶ constantFamily P X}
    (h : f.left ≫ prod.snd = g.left ≫ prod.snd) : f = g := constantFamily_hom_ext h

#print axioms CategoricalEssentialIncompleteness.V46.SliceProductCoordinates.lift_fst
#print axioms CategoricalEssentialIncompleteness.V46.constantFamily_hom_ext
