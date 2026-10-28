/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Dominical
import PCats.DominicalRecursion

/-!
# Signature guards for the dominical axioms

Each `example` fails to elaborate if a protected signature changes. The pinned
properties are claims about the instance telescope:

* `DiPaolaHeller.Dominical` assumes `Category`, `PCategoryStruct`, and
  `Limits.HasZeroMorphisms` alone.
* `DiPaolaHeller.Dominical.toPCategory` has no `PCategory` premise, and
  `DiPaolaHeller.Dominical.toProdominical` no `RecursionCategory.Prodominical`
  premise; a circular hypothesis would break the ascriptions.
* Neither conversion assumes `RecursionCategory.Isotype`: N1–N4 do not imply
  that all objects are isomorphic.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

#check @DiPaolaHeller.Dominical
#check @DiPaolaHeller.Dominical.toPCategory
#check @DiPaolaHeller.Dominical.toProdominical
#check @DiPaolaHeller.Dominical.eq_zero_iff_rst_eq_zero
#check @DiPaolaHeller.Dominical.isTotal_iff_rst_eq_id
#check @DiPaolaHeller.Dominical.isTotal_iff_restrictionTotal

/-! ### The class assumes the near-product data and zero morphisms alone -/

example : ∀ (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C], Prop :=
  fun C => DiPaolaHeller.Dominical C

/-! ### The conversions have no circular premise and assume no isotype -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C], DiPaolaHeller.Dominical C → PCategory C :=
  @DiPaolaHeller.Dominical.toPCategory

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C],
    DiPaolaHeller.Dominical C → RecursionCategory.Prodominical C :=
  @DiPaolaHeller.Dominical.toProdominical

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] (hd : DiPaolaHeller.Dominical C) :
    PCategory C :=
  hd.toPCategory

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] (hd : DiPaolaHeller.Dominical C) :
    RecursionCategory.Prodominical C :=
  hd.toProdominical

/-! ### N1 is the biconditional -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] (hd : DiPaolaHeller.Dominical C)
    {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    PCategoryStruct.nearProd_map f g = 0 ↔ f = 0 ∨ g = 0 :=
  hd.nearProd_eq_zero_iff f g

/-! ### N2 states a product on the Di Paola–Heller total subcategory -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] (hd : DiPaolaHeller.Dominical C)
    {Z X Y : C} (u : Z ⟶ X) (v : Z ⟶ Y)
    (hu : DiPaolaHeller.IsTotal u) (hv : DiPaolaHeller.IsTotal v) :
    ∃ h : Z ⟶ PCategoryStruct.nearProd X Y,
      (DiPaolaHeller.IsTotal h ∧ h ≫ PCategoryStruct.p0 X Y = u ∧
        h ≫ PCategoryStruct.p1 X Y = v) ∧
        ∀ h' : Z ⟶ PCategoryStruct.nearProd X Y, DiPaolaHeller.IsTotal h' →
          h' ≫ PCategoryStruct.p0 X Y = u →
          h' ≫ PCategoryStruct.p1 X Y = v → h' = h :=
  hd.existsUnique_pair u v hu hv

/-! ### Lemma 3.5(iii) needs neither `PCategory` nor `RestrictionCategory`

Both ascriptions carry `Category`, `PCategoryStruct`, and
`Limits.HasZeroMorphisms` only, and both conclusions are biconditionals. -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C], DiPaolaHeller.Dominical C →
    ∀ {X Y : C} (f : X ⟶ Y), f = 0 ↔ PCategoryStruct.rst f = 0 :=
  @DiPaolaHeller.Dominical.eq_zero_iff_rst_eq_zero

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C], DiPaolaHeller.Dominical C →
    ∀ {X Y : C} (f : X ⟶ Y),
      DiPaolaHeller.IsTotal f ↔ PCategoryStruct.rst f = 𝟙 X :=
  @DiPaolaHeller.Dominical.isTotal_iff_rst_eq_id

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] (hd : DiPaolaHeller.Dominical C) {X Y : C}
    (f : X ⟶ Y) : f = 0 ↔ PCategoryStruct.rst f = 0 :=
  hd.eq_zero_iff_rst_eq_zero f

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] (hd : DiPaolaHeller.Dominical C) {X Y : C}
    (f : X ⟶ Y) : DiPaolaHeller.IsTotal f ↔ PCategoryStruct.rst f = 𝟙 X :=
  hd.isTotal_iff_rst_eq_id f

/-! ### The comparison of the two totalities -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [Limits.HasZeroMorphisms C], DiPaolaHeller.Dominical C →
    ∀ {X Y : C} (f : X ⟶ Y),
      DiPaolaHeller.IsTotal f ↔ RestrictionCategory.isTotal f :=
  @DiPaolaHeller.Dominical.isTotal_iff_restrictionTotal

end CategoryTheory
