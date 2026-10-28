/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.PCat

/-!
# Dominical categories

Di Paola–Heller totality is zero-reflection: `f` is total when `γf = 0` forces
`γ = 0`. It is defined against `Category` and `Limits.HasZeroMorphisms`, before
any product structure.

`Dominical` states the axioms N1–N4 over the raw near-product data of
`PCategoryStruct`, with zero morphisms. It assumes neither `PCategory` nor
`RestrictionCategory`, and carries no isotype, semigroupoid, or Turing data.

* Bifunctoriality of `⊠`, as `nearProd_id` and `nearProd_comp`.
* N1: `f ⊠ g = 0` if and only if `f = 0` or `g = 0`.
* N2: the near product is a binary product on the subcategory of
  Di Paola–Heller total morphisms. The projections and the diagonal are total,
  `⊠` preserves totality, the diagonal has the two projection equations, a
  product of total morphisms commutes with the projections, and a pair of total
  morphisms has a unique total mediating morphism.
* N3: naturality of `assoc` and `swap` on arbitrary morphisms.
* N4: half-naturality of the projections and naturality of the diagonal, on
  arbitrary morphisms.

`Dominical.toPCategory` derives the `P`-category axioms. Nine of the fourteen
`PCategory` fields are supplied directly. The remaining five are derived: the
four nested-projection identities and `diag_p0_p1`. The nested-projection
identities follow from the N2 projection equations for a product of total
morphisms, applied with an identity in one argument. The identity `diag_p0_p1`
follows from N2 uniqueness: the two candidate mediating morphisms are total and
have projections `p0` and `p1`.

Lemma 3.5(iii) is `Dominical.eq_zero_iff_rst_eq_zero` and
`Dominical.isTotal_iff_rst_eq_id`: a morphism vanishes exactly when its
restriction does, and is Di Paola–Heller total exactly when its restriction is
the identity. Neither assumes `PCategory`; both install `toPCategory` locally.
`Dominical.isTotal_iff_restrictionTotal` states the second as the comparison of
the two totalities.
-/

universe v u

namespace CategoryTheory

namespace DiPaolaHeller

open PCategoryStruct

/-! ### Di Paola–Heller totality -/

section Total

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/-- Di Paola–Heller totality, the appendix's weak totality: `f` reflects zero. -/
def IsTotal {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ {W : C} (γ : W ⟶ X), γ ≫ f = 0 → γ = 0

/-- Identities are Di Paola–Heller total. -/
lemma isTotal_id (X : C) : IsTotal (𝟙 X) := by
  intro W γ h
  rwa [Category.comp_id] at h

/-- Di Paola–Heller total morphisms are closed under composition. -/
lemma IsTotal.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsTotal f) (hg : IsTotal g) : IsTotal (f ≫ g) := by
  intro W γ h
  refine hf γ (hg (γ ≫ f) ?_)
  rwa [Category.assoc]

/-- The forward morphism of an isomorphism is Di Paola–Heller total. The `inv`
field of the `Iso` supplies the retraction. -/
lemma isTotal_hom {X Y : C} (u : X ≅ Y) : IsTotal u.hom := by
  intro W γ h
  calc γ = γ ≫ 𝟙 X := (Category.comp_id γ).symm
    _ = γ ≫ u.hom ≫ u.inv := by rw [u.hom_inv_id]
    _ = (γ ≫ u.hom) ≫ u.inv := (Category.assoc _ _ _).symm
    _ = (0 : W ⟶ Y) ≫ u.inv := by rw [h]
    _ = 0 := Limits.zero_comp

/-- The inverse morphism of an isomorphism is Di Paola–Heller total. -/
lemma isTotal_inv {X Y : C} (u : X ≅ Y) : IsTotal u.inv := by
  intro W γ h
  calc γ = γ ≫ 𝟙 Y := (Category.comp_id γ).symm
    _ = γ ≫ u.inv ≫ u.hom := by rw [u.inv_hom_id]
    _ = (γ ≫ u.inv) ≫ u.hom := (Category.assoc _ _ _).symm
    _ = (0 : W ⟶ X) ≫ u.hom := by rw [h]
    _ = 0 := Limits.zero_comp

end Total

/-! ### The dominical axioms -/

open PCategoryStruct in
/-- A dominical category: the axioms N1–N4 over the near-product data of
`PCategoryStruct` together with zero morphisms. -/
class Dominical (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [Limits.HasZeroMorphisms C] : Prop where
  -- Bifunctoriality of `⊠`.
  nearProd_id : ∀ (X Y : C), nearProd_map (𝟙 X) (𝟙 Y) = 𝟙 (nearProd X Y)
  nearProd_comp : ∀ {U V W X Y Z : C} (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z),
    nearProd_map f h ≫ nearProd_map g k = nearProd_map (f ≫ g) (h ≫ k)
  /-- N1: `f ⊠ g` vanishes exactly when one factor does. -/
  nearProd_eq_zero_iff : ∀ {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z),
    nearProd_map f g = 0 ↔ f = 0 ∨ g = 0
  /-- N2: `⊠` preserves Di Paola–Heller totality. -/
  isTotal_nearProd_map : ∀ {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z},
    IsTotal f → IsTotal g → IsTotal (nearProd_map f g)
  /-- N2: the first projection is total. -/
  isTotal_p0 : ∀ (X Y : C), IsTotal (p0 X Y)
  /-- N2: the second projection is total. -/
  isTotal_p1 : ∀ (X Y : C), IsTotal (p1 X Y)
  /-- N2: the diagonal is total. -/
  isTotal_diag : ∀ (X : C), IsTotal (diag X)
  /-- N2: the diagonal followed by the first projection. -/
  diag_p0 : ∀ (X : C), diag X ≫ p0 X X = 𝟙 X
  /-- N2: the diagonal followed by the second projection. -/
  diag_p1 : ∀ (X : C), diag X ≫ p1 X X = 𝟙 X
  /-- N2: a product of total morphisms commutes with the first projection. -/
  nearProd_map_p0 : ∀ {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z},
    IsTotal f → IsTotal g → nearProd_map f g ≫ p0 X Z = p0 W Y ≫ f
  /-- N2: a product of total morphisms commutes with the second projection. -/
  nearProd_map_p1 : ∀ {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z},
    IsTotal f → IsTotal g → nearProd_map f g ≫ p1 X Z = p1 W Y ≫ g
  /-- N2: a pair of total morphisms has a unique total mediating morphism.
  Uniqueness is among total mediating morphisms. -/
  existsUnique_pair : ∀ {Z X Y : C} (u : Z ⟶ X) (v : Z ⟶ Y),
    IsTotal u → IsTotal v →
      ∃ h : Z ⟶ nearProd X Y,
        (IsTotal h ∧ h ≫ p0 X Y = u ∧ h ≫ p1 X Y = v) ∧
          ∀ h' : Z ⟶ nearProd X Y, IsTotal h' →
            h' ≫ p0 X Y = u → h' ≫ p1 X Y = v → h' = h
  /-- N3: naturality of the associativity morphism. -/
  assoc_nat : ∀ {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    nearProd_map (nearProd_map f g) h ≫ assoc X' Y' Z'
      = assoc X Y Z ≫ nearProd_map f (nearProd_map g h)
  /-- N3: naturality of the symmetry. -/
  swap_nat : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    nearProd_map f g ≫ swap X' Y' = swap X Y ≫ nearProd_map g f
  /-- N4: half-naturality of the first projection. -/
  p0_nat : ∀ {X Y Z : C} (f : X ⟶ Y), nearProd_map f (𝟙 Z) ≫ p0 Y Z = p0 X Z ≫ f
  /-- N4: half-naturality of the second projection. -/
  p1_nat : ∀ {X Y Z : C} (f : X ⟶ Y), nearProd_map (𝟙 Z) f ≫ p1 Z Y = p1 Z X ≫ f
  /-- N4: naturality of the diagonal. -/
  diag_nat : ∀ {X Y : C} (f : X ⟶ Y), f ≫ diag Y = diag X ≫ nearProd_map f f

/-! ### The induced `P`-category -/

section ToPCategory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C]
  [Limits.HasZeroMorphisms C]

/-- The `P`-category axioms hold in a dominical category. Not an instance. -/
theorem Dominical.toPCategory (hd : Dominical C) : PCategory C where
  nearProd_id := hd.nearProd_id
  nearProd_comp := hd.nearProd_comp
  diag_p0 := hd.diag_p0
  diag_p1 := hd.diag_p1
  diag_p0_p1 := by
    intro X Y
    obtain ⟨k, -, huniq⟩ := hd.existsUnique_pair (p0 X Y) (p1 X Y)
      (hd.isTotal_p0 X Y) (hd.isTotal_p1 X Y)
    have hmap : IsTotal (nearProd_map (p0 X Y) (p1 X Y)) :=
      hd.isTotal_nearProd_map (hd.isTotal_p0 X Y) (hd.isTotal_p1 X Y)
    have ha : IsTotal
        (diag (nearProd X Y) ≫ nearProd_map (p0 X Y) (p1 X Y)) :=
      IsTotal.comp (hd.isTotal_diag _) hmap
    have ha0 : (diag (nearProd X Y) ≫ nearProd_map (p0 X Y) (p1 X Y))
        ≫ p0 X Y = p0 X Y := by
      rw [Category.assoc,
        hd.nearProd_map_p0 (hd.isTotal_p0 X Y) (hd.isTotal_p1 X Y),
        ← Category.assoc, hd.diag_p0, Category.id_comp]
    have ha1 : (diag (nearProd X Y) ≫ nearProd_map (p0 X Y) (p1 X Y))
        ≫ p1 X Y = p1 X Y := by
      rw [Category.assoc,
        hd.nearProd_map_p1 (hd.isTotal_p0 X Y) (hd.isTotal_p1 X Y),
        ← Category.assoc, hd.diag_p1, Category.id_comp]
    exact (huniq _ ha ha0 ha1).trans
      (huniq _ (isTotal_id _) (Category.id_comp _) (Category.id_comp _)).symm
  p0_p0 := by
    intro X Y Z
    have h := hd.nearProd_map_p0 (isTotal_id X) (hd.isTotal_p0 Y Z)
    rwa [Category.comp_id] at h
  p0_p1 := by
    intro X Y Z
    have h := hd.nearProd_map_p0 (isTotal_id X) (hd.isTotal_p1 Y Z)
    rwa [Category.comp_id] at h
  p1_p0 := by
    intro X Y Z
    have h := hd.nearProd_map_p1 (hd.isTotal_p0 X Y) (isTotal_id Z)
    rwa [Category.comp_id] at h
  p1_p1 := by
    intro X Y Z
    have h := hd.nearProd_map_p1 (hd.isTotal_p1 X Y) (isTotal_id Z)
    rwa [Category.comp_id] at h
  diag_nat := hd.diag_nat
  p0_nat := hd.p0_nat
  p1_nat := hd.p1_nat
  assoc_nat := hd.assoc_nat
  swap_nat := hd.swap_nat

/-! ### Lemma 3.5(iii) -/

/-- A morphism vanishes exactly when its restriction does. Left to right is N1
applied to `𝟙 X ⊠ 0`; right to left is R1. -/
theorem Dominical.eq_zero_iff_rst_eq_zero (hd : Dominical C) {X Y : C}
    (f : X ⟶ Y) : f = 0 ↔ PCategoryStruct.rst f = 0 := by
  constructor
  · rintro rfl
    dsimp only [PCategoryStruct.rst]
    rw [(hd.nearProd_eq_zero_iff (𝟙 X) (0 : X ⟶ Y)).mpr (Or.inr rfl),
      Limits.zero_comp, Limits.comp_zero]
  · intro h
    let : PCategory C := hd.toPCategory
    have h1 : PCategoryStruct.rst f ≫ f = f := RestrictionCategory.rst_comp_self f
    rw [h, Limits.zero_comp] at h1
    exact h1.symm

/-- Di Paola–Heller totality is restriction totality. Left to right is the N2
projection equation at `𝟙 X` and `f` followed by `diag_p0`; right to left
reflects zero through `eq_zero_iff_rst_eq_zero` and `rst_comp_of_isTotal'`. -/
theorem Dominical.isTotal_iff_rst_eq_id (hd : Dominical C) {X Y : C}
    (f : X ⟶ Y) : IsTotal f ↔ PCategoryStruct.rst f = 𝟙 X := by
  constructor
  · intro hf
    dsimp only [PCategoryStruct.rst]
    rw [hd.nearProd_map_p0 (isTotal_id X) hf, Category.comp_id, hd.diag_p0]
  · intro h W γ hγ
    let : PCategory C := hd.toPCategory
    have h0 : PCategoryStruct.rst (γ ≫ f) = 0 :=
      (hd.eq_zero_iff_rst_eq_zero (γ ≫ f)).mp hγ
    have h1 : PCategoryStruct.rst (γ ≫ f) = PCategoryStruct.rst γ :=
      PCategory.rst_comp_of_isTotal' γ h
    rw [h1] at h0
    exact (hd.eq_zero_iff_rst_eq_zero γ).mpr h0

end ToPCategory

/-! ### The comparison of the two totalities -/

section Comparison

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
  [Limits.HasZeroMorphisms C]

/-- In a dominical category the two notions of totality agree. -/
theorem Dominical.isTotal_iff_restrictionTotal (hd : Dominical C) {X Y : C}
    (f : X ⟶ Y) : IsTotal f ↔ RestrictionCategory.isTotal f :=
  hd.isTotal_iff_rst_eq_id f

end Comparison

end DiPaolaHeller

end CategoryTheory
