/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSyntax

/-! # Coordinates of products in a slice category

These equations keep product identities in the slice before applying the
underlying-object functor.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SliceProductCoordinates

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] {P : D}
variable {W X Y X' Y' : Over P}

@[reassoc (attr := simp)] theorem lift_fst (f : W ⟶ X) (g : W ⟶ Y) :
    (prod.lift f g).left ≫ (prod.fst : X ⨯ Y ⟶ X).left = f.left :=
  congrArg Over.Hom.left (prod.lift_fst f g)

@[reassoc (attr := simp)] theorem lift_snd (f : W ⟶ X) (g : W ⟶ Y) :
    (prod.lift f g).left ≫ (prod.snd : X ⨯ Y ⟶ Y).left = g.left :=
  congrArg Over.Hom.left (prod.lift_snd f g)

@[reassoc (attr := simp)] theorem map_fst (f : X ⟶ X') (g : Y ⟶ Y') :
    (prod.map f g).left ≫ (prod.fst : X' ⨯ Y' ⟶ X').left =
      (prod.fst : X ⨯ Y ⟶ X).left ≫ f.left :=
  congrArg Over.Hom.left (prod.map_fst f g)

@[reassoc (attr := simp)] theorem map_snd (f : X ⟶ X') (g : Y ⟶ Y') :
    (prod.map f g).left ≫ (prod.snd : X' ⨯ Y' ⟶ Y').left =
      (prod.snd : X ⨯ Y ⟶ Y).left ≫ g.left :=
  congrArg Over.Hom.left (prod.map_snd f g)

end CategoricalEssentialIncompleteness.V46.SliceProductCoordinates

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] {P X : D} {W : Over P}

@[reassoc (attr := simp)] theorem constantFamily_parameter (f : W ⟶ constantFamily P X) :
    f.left ≫ prod.fst = W.hom := Over.w f

@[reassoc] theorem constantProduct_fst_parameter (P X Y : D) :
    (prod.fst : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P X).left ≫
      prod.fst = (constantFamily P X ⨯ constantFamily P Y).hom := Over.w _

@[reassoc] theorem constantProduct_snd_parameter (P X Y : D) :
    (prod.snd : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P Y).left ≫
      prod.fst = (constantFamily P X ⨯ constantFamily P Y).hom := Over.w _

theorem constantFamily_hom_ext {f g : W ⟶ constantFamily P X}
    (h : f.left ≫ prod.snd = g.left ≫ prod.snd) : f = g := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w f).trans (Over.w g).symm
  · exact h

end CategoricalEssentialIncompleteness.V46
