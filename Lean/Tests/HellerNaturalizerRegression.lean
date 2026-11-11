/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.HellerNaturalizer

/-!
# Signature guards for the projection-generated subcategory

Exact `@`-ascriptions guard the ten public telescopes. Applied examples guard
membership of the projections, identity and composition membership through the
named multiplicative instance, closure under `nearProd_map`, leastness against
an arbitrary multiplicative property, totality of a generated morphism, both
naturality equations, and the wide subcategory. The closure guards assume only
`[Category C]` and `[PCategoryStruct C]`; `[PCategory C]` appears only for
totality and naturality. `check_axioms.lean` audits axiom dependencies.

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

#check @PCategory.projectionGenerated
#check @PCategory.projectionGenerated_p0
#check @PCategory.projectionGenerated_p1
#check @PCategory.projectionGenerated_nearProd_map
#check @PCategory.instIsMultiplicativeProjectionGenerated
#check @PCategory.ProjectionSubcategory
#check @PCategory.projectionGenerated_le
#check @PCategory.projectionGenerated_isTotal
#check @PCategory.p0_nat_of_projectionGenerated
#check @PCategory.p1_nat_of_projectionGenerated

/-! ### The closure, under `[Category]` and `[PCategoryStruct]` only -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C],
    MorphismProperty C :=
  @PCategory.projectionGenerated

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] (X Y : C),
    PCategory.projectionGenerated (p0 X Y) :=
  @PCategory.projectionGenerated_p0

example {C : Type u} [Category.{v} C] [PCategoryStruct C] (X Y : C) :
    PCategory.projectionGenerated (p0 X Y) :=
  PCategory.projectionGenerated_p0 X Y

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] (X Y : C),
    PCategory.projectionGenerated (p1 X Y) :=
  @PCategory.projectionGenerated_p1

example {C : Type u} [Category.{v} C] [PCategoryStruct C] (X Y : C) :
    PCategory.projectionGenerated (p1 X Y) :=
  PCategory.projectionGenerated_p1 X Y

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z}, PCategory.projectionGenerated f →
    PCategory.projectionGenerated g →
    PCategory.projectionGenerated (nearProd_map f g) :=
  @PCategory.projectionGenerated_nearProd_map

example {C : Type u} [Category.{v} C] [PCategoryStruct C] {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z} (hf : PCategory.projectionGenerated f)
    (hg : PCategory.projectionGenerated g) :
    PCategory.projectionGenerated (nearProd_map f g) :=
  PCategory.projectionGenerated_nearProd_map hf hg

/-! ### Identities and composition through the named instance -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C],
    (PCategory.projectionGenerated (C := C)).IsMultiplicative :=
  @PCategory.instIsMultiplicativeProjectionGenerated

example {C : Type u} [Category.{v} C] [PCategoryStruct C] :
    (PCategory.projectionGenerated (C := C)).IsMultiplicative :=
  inferInstance

example {C : Type u} [Category.{v} C] [PCategoryStruct C] (X : C) :
    PCategory.projectionGenerated (𝟙 X) :=
  MorphismProperty.id_mem PCategory.projectionGenerated X

example {C : Type u} [Category.{v} C] [PCategoryStruct C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : PCategory.projectionGenerated f)
    (hg : PCategory.projectionGenerated g) :
    PCategory.projectionGenerated (f ≫ g) :=
  MorphismProperty.comp_mem PCategory.projectionGenerated f g hf hg

/-! ### The wide subcategory -/

example : ∀ (C : Type u) [Category.{v} C] [PCategoryStruct C], Type u :=
  @PCategory.ProjectionSubcategory

example {C : Type u} [Category.{v} C] [PCategoryStruct C] (X : C) :
    PCategory.ProjectionSubcategory C :=
  ⟨X⟩

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    {X Y : PCategory.ProjectionSubcategory C} (u : X ⟶ Y) :
    PCategory.projectionGenerated u.hom :=
  u.property

/-! ### Leastness, in the pointwise formulation -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C]
    (M : MorphismProperty C) [M.IsMultiplicative],
    (∀ (X Y : C), M (p0 X Y)) → (∀ (X Y : C), M (p1 X Y)) →
    (∀ {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z},
      M f → M g → M (nearProd_map f g)) →
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      PCategory.projectionGenerated (C := C) f → M f :=
  @PCategory.projectionGenerated_le

example {C : Type u} [Category.{v} C] [PCategoryStruct C]
    (M : MorphismProperty C) [M.IsMultiplicative]
    (hp0 : ∀ X Y, M (p0 X Y)) (hp1 : ∀ X Y, M (p1 X Y))
    (hprod : ∀ {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z},
      M f → M g → M (nearProd_map f g))
    {X Y : C} (f : X ⟶ Y) (hf : PCategory.projectionGenerated f) : M f :=
  PCategory.projectionGenerated_le M hp0 hp1 hprod f hf

/-! ### Totality and naturality, adding `[PCategory]` -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : C} {f : X ⟶ Y}, PCategory.projectionGenerated f →
    RestrictionCategory.isTotal f :=
  @PCategory.projectionGenerated_isTotal

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : C} {f : X ⟶ Y} (hf : PCategory.projectionGenerated f) :
    RestrictionCategory.isTotal f :=
  PCategory.projectionGenerated_isTotal hf

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {W X Y Z : C} (f : W ⟶ X) {g : Y ⟶ Z},
    PCategory.projectionGenerated g →
    nearProd_map f g ≫ p0 X Z = p0 W Y ≫ f :=
  @PCategory.p0_nat_of_projectionGenerated

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {W X Y Z : C} (f : W ⟶ X) {g : Y ⟶ Z}
    (hg : PCategory.projectionGenerated g) :
    nearProd_map f g ≫ p0 X Z = p0 W Y ≫ f :=
  PCategory.p0_nat_of_projectionGenerated f hg

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {W X Y Z : C} {f : W ⟶ X} (g : Y ⟶ Z),
    PCategory.projectionGenerated f →
    nearProd_map f g ≫ p1 X Z = p1 W Y ≫ g :=
  @PCategory.p1_nat_of_projectionGenerated

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {W X Y Z : C} {f : W ⟶ X} (g : Y ⟶ Z)
    (hf : PCategory.projectionGenerated f) :
    nearProd_map f g ≫ p1 X Z = p1 W Y ≫ g :=
  PCategory.p1_nat_of_projectionGenerated g hf

/-- The two naturalizer containments at a projection in the generated
coordinate. -/
example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {W X : C} (f : W ⟶ X) (Y Z : C) :
    (nearProd_map f (p0 Y Z) ≫ p0 X Y = p0 W (nearProd Y Z) ≫ f)
      ∧ (nearProd_map (p0 Y Z) f ≫ p1 Y X = p1 (nearProd Y Z) W ≫ f) :=
  ⟨PCategory.p0_nat_of_projectionGenerated f
      (PCategory.projectionGenerated_p0 Y Z),
    PCategory.p1_nat_of_projectionGenerated f
      (PCategory.projectionGenerated_p0 Y Z)⟩

end CategoryTheory
