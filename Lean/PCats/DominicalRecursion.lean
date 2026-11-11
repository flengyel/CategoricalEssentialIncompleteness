/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Dominical
public import PCats.Recursion

/-!
# Fixed-source Turing data

`Dominical.toProdominical` derives zero absorption from N1.

`FixedSourceTuringData` carries objects `W`, `X`, `Y` and a morphism
`τ : W ⊠ X ⟶ Y` whose factorization property is stated at the fixed source
`W ⊠ X`, and assumes `Category`, `PCategoryStruct`, and
`Limits.HasZeroMorphisms`. `RecursionCategory.IsTuringMorphism` quantifies
instead over every source object. `IsTuringMorphism.toRecursionCategory` derives
the quantified form from the fixed-source form in an isotype, under
`TotalityImpliesRestrictionTotal`; this is the transport at Appendix A, lines
381–388.

The generic morphism transport assumes `PCategory`, `Isotype`, and
`TotalityImpliesRestrictionTotal`. The generic `PRecursionCategory` packaging
additionally assumes `Prodominical`. `Dominical.toPCategory` and
`Dominical.toProdominical` supply `PCategory` and `Prodominical` from N1–N4,
and `Dominical.totalityImpliesRestrictionTotal` supplies the comparison from
Lemma 3.5(iii); the semigroupoid condition supplies `Isotype`.

`Dominical.toPRecursionCategory` is Proposition A.5: dominical data, an
isotype, and fixed-source Turing data yield a `P`-recursion category. Its result
type names `toPCategory` and `toProdominical`, which `PRecursionCategory` takes
as instance parameters.

Elimination of `Nonempty (W ≅ V)` occurs inside a proposition and does not
introduce `Classical.choice`. The inverse used is the `inv` field of `Iso`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace DiPaolaHeller

open PCategoryStruct

/-! ### Zero absorption -/

section Prodominical

variable {C : Type u} [Category.{v} C] [PCategoryStruct C]
  [Limits.HasZeroMorphisms C]

/-- A dominical category is prodominical. Both zero-absorption equations are the
right-to-left direction of N1. Not an instance. -/
theorem Dominical.toProdominical (hd : Dominical C) :
    RecursionCategory.Prodominical C where
  nearProd_zero_right f := (hd.nearProd_eq_zero_iff f 0).mpr (Or.inr rfl)
  nearProd_zero_left f := (hd.nearProd_eq_zero_iff 0 f).mpr (Or.inl rfl)

end Prodominical

/-! ### Fixed-source Turing data -/

section Data

variable {C : Type u} [Category.{v} C] [PCategoryStruct C]
  [Limits.HasZeroMorphisms C]

/-- The fixed-source Di Paola–Heller Turing property: every
`φ : W ⊠ X ⟶ Y` factors through `τ` along a Di Paola–Heller total `h : W ⟶ W`.
The source object is fixed, where `RecursionCategory.IsTuringMorphism`
quantifies over it. -/
def IsTuringMorphism {W X Y : C} (τ : nearProd W X ⟶ Y) : Prop :=
  ∀ φ : nearProd W X ⟶ Y,
    ∃ h : W ⟶ W, IsTotal h ∧ nearProd_map h (𝟙 X) ≫ τ = φ

/-- Objects and a morphism satisfying the fixed-source Di Paola–Heller Turing
property. -/
class FixedSourceTuringData (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] where
  /-- The index object. -/
  W : C
  /-- The argument object. -/
  X : C
  /-- The value object. -/
  Y : C
  /-- The Turing morphism. -/
  tau : nearProd W X ⟶ Y
  /-- `tau` has the fixed-source Di Paola–Heller Turing property. -/
  is_turing : IsTuringMorphism tau

end Data

/-! ### The comparison of the two totalities -/

/-- Every Di Paola–Heller total morphism is restriction-total. -/
def TotalityImpliesRestrictionTotal (C : Type u) [Category.{v} C]
    [PCategoryStruct C] [PCategory C] [Limits.HasZeroMorphisms C] : Prop :=
  ∀ {A B : C} (f : A ⟶ B), IsTotal f → RestrictionCategory.isTotal f

/-- A dominical category satisfies the comparison, by Lemma 3.5(iii). -/
theorem Dominical.totalityImpliesRestrictionTotal {C : Type u} [Category.{v} C]
    [PCategoryStruct C] [PCategory C] [Limits.HasZeroMorphisms C]
    (hd : Dominical C) : TotalityImpliesRestrictionTotal C :=
  fun f hf => (hd.isTotal_iff_restrictionTotal f).mp hf

/-! ### Transport to the `P`-categorical Turing property -/

section Transport

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Isotype C]

/-- In an isotype, a fixed-source Di Paola–Heller Turing morphism satisfies the
`P`-categorical Turing property when Di Paola–Heller total morphisms are
restriction-total.

For `φ : V ⊠ X ⟶ Y`, an isomorphism `u : W ≅ V` reindexes it to
`(u ⊠ 1)φ : W ⊠ X ⟶ Y`; the fixed-source property supplies `h`, and
`g = u⁻¹h` factors `φ` through `τ`. -/
theorem IsTuringMorphism.toRecursionCategory {W X Y : C}
    {τ : nearProd W X ⟶ Y} (hτ : IsTuringMorphism τ)
    (hcomp : TotalityImpliesRestrictionTotal C) :
    RecursionCategory.IsTuringMorphism τ := by
  intro V φ
  obtain ⟨u⟩ := RecursionCategory.Isotype.iso W V
  obtain ⟨h, hh, hfac⟩ := hτ (nearProd_map u.hom (𝟙 X) ≫ φ)
  refine ⟨u.inv ≫ h, RestrictionCategory.isTotal_comp
    (hcomp _ (isTotal_inv u)) (hcomp _ hh), ?_⟩
  calc nearProd_map (u.inv ≫ h) (𝟙 X) ≫ τ
      = (nearProd_map u.inv (𝟙 X) ≫ nearProd_map h (𝟙 X)) ≫ τ := by
        rw [PCategory.nearProd_comp, Category.comp_id]
    _ = nearProd_map u.inv (𝟙 X) ≫ nearProd_map h (𝟙 X) ≫ τ :=
        Category.assoc _ _ _
    _ = nearProd_map u.inv (𝟙 X) ≫ nearProd_map u.hom (𝟙 X) ≫ φ := by rw [hfac]
    _ = (nearProd_map u.inv (𝟙 X) ≫ nearProd_map u.hom (𝟙 X)) ≫ φ :=
        (Category.assoc _ _ _).symm
    _ = nearProd_map (u.inv ≫ u.hom) (𝟙 X ≫ 𝟙 X) ≫ φ := by
        rw [PCategory.nearProd_comp]
    _ = φ := by
        rw [u.inv_hom_id, Category.comp_id, PCategory.nearProd_id,
          Category.id_comp]

end Transport

/-! ### The induced `P`-recursion category -/

section Induced

variable (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]
  [RecursionCategory.Isotype C] [FixedSourceTuringData C]

/-- Constructs a `P`-recursion category from fixed-source Turing data under the
`P`-category, prodominical, isotype, and totality-comparison hypotheses.

Reducible because the result type is a class. It is not an instance: the
totality comparison is supplied at each use. -/
@[reducible] def FixedSourceTuringData.toPRecursionCategory
    (hcomp : TotalityImpliesRestrictionTotal C) :
    RecursionCategory.PRecursionCategory C where
  W := FixedSourceTuringData.W (C := C)
  X := FixedSourceTuringData.X (C := C)
  Y := FixedSourceTuringData.Y (C := C)
  tau := FixedSourceTuringData.tau (C := C)
  is_turing := (FixedSourceTuringData.is_turing (C := C)).toRecursionCategory hcomp

end Induced

/-! ### Proposition A.5 -/

section PropositionA5

variable {C : Type u} [Category.{v} C] [PCategoryStruct C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Isotype C]
  [FixedSourceTuringData C]

/-- Proposition A.5: a Di Paola–Heller recursion category is a `P`-recursion
category. N1–N4 supply the `P`-category and prodominical structures and, by
Lemma 3.5(iii), the totality comparison; the isotype hypothesis is the
semigroupoid condition. The result type names the derived structures, since
`PRecursionCategory` takes them as instance parameters. Not an instance. -/
@[reducible] def Dominical.toPRecursionCategory (hd : Dominical C) :
    @RecursionCategory.PRecursionCategory C _ _ hd.toPCategory _
      hd.toProdominical _ := by
  letI : PCategory C := hd.toPCategory
  letI : RecursionCategory.Prodominical C := hd.toProdominical
  exact FixedSourceTuringData.toPRecursionCategory C
    hd.totalityImpliesRestrictionTotal

end PropositionA5

end DiPaolaHeller

end CategoryTheory
