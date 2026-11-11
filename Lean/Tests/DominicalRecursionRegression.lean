/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.DominicalRecursion

/-!
# Signature guards for `PCats.DominicalRecursion`

Each `example` fails to elaborate if a protected signature changes. Two
properties are claims about the instance telescope and are pinned by
`@`-ascription:

* `DiPaolaHeller.IsTotal` assumes `Category` and `Limits.HasZeroMorphisms`
  alone, so adding `PCategoryStruct` or `PCategory` breaks this file.
* `DiPaolaHeller.FixedSourceTuringData` assumes `Category`, `PCategoryStruct`,
  and `Limits.HasZeroMorphisms` alone, so adding `PCategory`, `Prodominical`,
  or `Isotype` breaks this file.

The two generic conversions
`DiPaolaHeller.IsTuringMorphism.toRecursionCategory` and
`DiPaolaHeller.FixedSourceTuringData.toPRecursionCategory` take
`DiPaolaHeller.TotalityImpliesRestrictionTotal` as an explicit argument, so
promoting it to an instance or discharging it breaks this file.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open PCategoryStruct

#check @DiPaolaHeller.IsTotal
#check @DiPaolaHeller.IsTuringMorphism
#check @DiPaolaHeller.FixedSourceTuringData
#check @DiPaolaHeller.TotalityImpliesRestrictionTotal
#check @DiPaolaHeller.IsTuringMorphism.toRecursionCategory
#check @DiPaolaHeller.FixedSourceTuringData.toPRecursionCategory

/-! ### Totality precedes the product structure -/

example : ∀ {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
    {X Y : C}, (X ⟶ Y) → Prop :=
  @DiPaolaHeller.IsTotal

example : ∀ {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] (X : C),
    DiPaolaHeller.IsTotal (𝟙 X) :=
  @DiPaolaHeller.isTotal_id

example {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] {X Y Z : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : DiPaolaHeller.IsTotal f)
    (hg : DiPaolaHeller.IsTotal g) : DiPaolaHeller.IsTotal (f ≫ g) :=
  hf.comp hg

/-! ### Both halves of an isomorphism are total -/

example {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] {X Y : C}
    (u : X ≅ Y) : DiPaolaHeller.IsTotal u.hom :=
  DiPaolaHeller.isTotal_hom u

example {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] {X Y : C}
    (u : X ≅ Y) : DiPaolaHeller.IsTotal u.inv :=
  DiPaolaHeller.isTotal_inv u

/-! ### The fixed-source Turing property -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] {W X Y : C} (τ : nearProd W X ⟶ Y) :
    DiPaolaHeller.IsTuringMorphism τ ↔
      ∀ φ : nearProd W X ⟶ Y,
        ∃ h : W ⟶ W, DiPaolaHeller.IsTotal h ∧
          nearProd_map h (𝟙 X) ≫ τ = φ :=
  Iff.rfl

/-! ### The data class assumes no `P`-category axioms -/

example : ∀ (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C], Type _ :=
  fun C => DiPaolaHeller.FixedSourceTuringData C

/-! ### The totality comparison -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [Limits.HasZeroMorphisms C] :
    DiPaolaHeller.TotalityImpliesRestrictionTotal C ↔
      ∀ {A B : C} (f : A ⟶ B),
        DiPaolaHeller.IsTotal f → RestrictionCategory.isTotal f :=
  Iff.rfl

/-! ### The two conversions -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Isotype C]
    {W X Y : C} {τ : nearProd W X ⟶ Y}
    (hτ : DiPaolaHeller.IsTuringMorphism τ)
    (hcomp : DiPaolaHeller.TotalityImpliesRestrictionTotal C) :
    RecursionCategory.IsTuringMorphism τ :=
  hτ.toRecursionCategory hcomp

example (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]
    [RecursionCategory.Isotype C] [DiPaolaHeller.FixedSourceTuringData C]
    (hcomp : DiPaolaHeller.TotalityImpliesRestrictionTotal C) :
    RecursionCategory.PRecursionCategory C :=
  DiPaolaHeller.FixedSourceTuringData.toPRecursionCategory C hcomp

/-! ### A dominical category discharges the comparison -/

#check @DiPaolaHeller.Dominical.totalityImpliesRestrictionTotal
#check @DiPaolaHeller.Dominical.toPRecursionCategory

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [Limits.HasZeroMorphisms C] (hd : DiPaolaHeller.Dominical C) :
    DiPaolaHeller.TotalityImpliesRestrictionTotal C :=
  hd.totalityImpliesRestrictionTotal

/-! ### Proposition A.5

The telescope carries no `PCategory`, no `RecursionCategory.Prodominical`, and
no comparison hypothesis; `RecursionCategory.Isotype` remains separate, and the
result type names the derived structures. -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Isotype C]
    [DiPaolaHeller.FixedSourceTuringData C] (hd : DiPaolaHeller.Dominical C),
    @RecursionCategory.PRecursionCategory C _ _ hd.toPCategory _
      hd.toProdominical _ :=
  @DiPaolaHeller.Dominical.toPRecursionCategory

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Isotype C]
    [DiPaolaHeller.FixedSourceTuringData C]
    (hd : DiPaolaHeller.Dominical C) :
    @RecursionCategory.PRecursionCategory C _ _ hd.toPCategory _
      hd.toProdominical _ :=
  hd.toPRecursionCategory

end CategoryTheory
