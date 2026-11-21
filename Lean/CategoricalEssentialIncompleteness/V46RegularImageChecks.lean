/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RegularImage


/-! # Initial derivation algebras and their images -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory

universe v u

namespace CategoricalEssentialIncompleteness.V46.StatementChecks

example {D : Type u} [Category.{v} D] [Regular D] {F : D}
    (H : Over F ⥤ Over F)
    (hH : ∀ {X Y : Over F} (e : X ⟶ Y), IsRegularEpi e.left →
      IsRegularEpi (H.map e).left)
    (A : Endofunctor.Algebra H) (hA : IsInitial A) :
    Nonempty (H.obj (Over.mk (image.ι A.a.hom)) ⟶ Over.mk (image.ι A.a.hom)) ∧
      ∀ {U : D} (m : U ⟶ F) [Mono m],
        Nonempty (H.obj (Over.mk m) ⟶ Over.mk m) →
          ∃ w : image A.a.hom ⟶ U, w ≫ m = image.ι A.a.hom :=
  least_closed_image H A hH hA

open LocalConnectedness LocalConnectedness.V46 in
example {S : Type u} [Category.{v} S] [RestrictionCategory S]
    [Ranges S] [Splits S]
    {X I Y : WideSubcategory (isTotal (C := S))}
    (e : X ⟶ I) (m : I ⟶ Y) [IsRegularEpi e]
    (r : Y.obj ⟶ I.obj) (hmr : m.hom ≫ r = 𝟙 I.obj)
    (hrm : r ≫ m.hom = rst r) :
    (Ranges.range (e.hom ≫ m.hom)).hom = r ≫ m.hom :=
  range_regularImage e m r hmr hrm

open LocalConnectedness LocalConnectedness.V46 in
example {S : Type u} [Category.{v} S] [RestrictionCategory S]
    [Ranges S] [Splits S]
    [Regular (WideSubcategory (isTotal (C := S)))]
    {X I Y : WideSubcategory (isTotal (C := S))}
    (f : X ⟶ Y) (e : X ⟶ I) (m : I ⟶ Y)
    [IsRegularEpi e] [Mono m] (hfac : e ≫ m = f)
    (r : Y.obj ⟶ I.obj) (hmr : m.hom ≫ r = 𝟙 I.obj)
    (hrm : r ≫ m.hom = rst r) :
    (Ranges.range f.hom).hom = r ≫ m.hom ∧ r ≫ m.hom = rst r := by
  constructor
  · rw [← hfac]
    exact range_regularImage e m r hmr hrm
  · exact hrm

end CategoricalEssentialIncompleteness.V46.StatementChecks
