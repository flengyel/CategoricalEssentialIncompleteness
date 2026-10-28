/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.DomEqualizers

/-!
# Signature guards for equalizers in `Dom C`

Each `example` fails to elaborate if a protected signature or equation changes.
Exact `@`-ascriptions pin the telescopes of `Dom.binaryProductDiagonal`,
`Dom.diagonalSubdomain`, `Dom.diagonalFactor`, `Dom.diagonalFactorIso`,
`Dom.equalizerSubdomain`, `Dom.equalizerObject`, `Dom.equalizerInclusion`,
`Dom.equalizerLift`, and `Dom.equalizer_existsUnique`; applied examples guard
the defining equations of the diagonal factor and of the equalizer object,
`Dom.equalizer_comm`, both inverse laws of `Dom.diagonalFactorIso`, and the
lift equation, its uniqueness, and the final `∃!` property.

Each guard writes out the whole telescope, so it fails to elaborate if any
hypothesis beyond `[HasRanges C]` — `IsRP`, a choice principle, a zero
morphism, dominical, prodominical, isotype, recursion, or limits structure —
enters a protected declaration. Classical axiom dependencies are not visible to
these guards and are checked separately by `check_axioms.lean`.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

#check @Dom.binaryProductDiagonal
#check @Dom.diagonalSubdomain
#check @Dom.diagonalFactor
#check @Dom.diagonalFactor_inclusion
#check @Dom.diagonalFactorIso
#check @Dom.diagonalSubdomain_fst_eq_snd
#check @Dom.equalizerSubdomain
#check @Dom.equalizerObject
#check @Dom.equalizerInclusion
#check @Dom.equalizer_comm
#check @Dom.equalizerLift
#check @Dom.equalizerLift_inclusion
#check @Dom.equalizerLift_unique
#check @Dom.equalizer_existsUnique

/-! ### The diagonal

`binaryProductDiagonal` is the diagonal of `Dom C` and needs no ranges. -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (B : Dom C), B ⟶ Dom.binaryProduct B B :=
  @Dom.binaryProductDiagonal

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (B : Dom C) :
    Dom.binaryProductDiagonal B = Dom.binaryProductLift (𝟙 B) (𝟙 B) :=
  rfl

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (B : Dom C) :
    Dom.binaryProductDiagonal B ≫ Dom.binaryProductFst B B = 𝟙 B :=
  Dom.binaryProductDiagonal_fst B

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (B : Dom C) :
    Dom.binaryProductDiagonal B ≫ Dom.binaryProductSnd B B = 𝟙 B :=
  Dom.binaryProductDiagonal_snd B

/-! ### The diagonal subdomain and its factor -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C), Dom.Subdomain (Dom.binaryProduct B B) :=
  @Dom.diagonalSubdomain

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C) :
    (Dom.diagonalSubdomain B).idem
      = HasRanges.ran (Dom.binaryProductDiagonal B).hom :=
  Dom.diagonalSubdomain_idem B

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C), B ⟶ (Dom.diagonalSubdomain B).toDom :=
  @Dom.diagonalFactor

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C) :
    (Dom.diagonalFactor B).hom = (Dom.binaryProductDiagonal B).hom :=
  Dom.diagonalFactor_hom B

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C),
    Dom.diagonalFactor B ≫ (Dom.diagonalSubdomain B).inclusion
      = Dom.binaryProductDiagonal B :=
  @Dom.diagonalFactor_inclusion

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C) :
    Dom.diagonalFactor B ≫ (Dom.diagonalSubdomain B).inclusion
      = Dom.binaryProductDiagonal B :=
  Dom.diagonalFactor_inclusion B

/-! ### The factor is an isomorphism -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C), B ≅ (Dom.diagonalSubdomain B).toDom :=
  @Dom.diagonalFactorIso

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C) :
    (Dom.diagonalFactorIso B).hom = Dom.diagonalFactor B :=
  rfl

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C) :
    (Dom.diagonalFactorIso B).inv
      = (Dom.diagonalSubdomain B).inclusion ≫ Dom.binaryProductFst B B :=
  rfl

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C) :
    (Dom.diagonalFactorIso B).hom ≫ (Dom.diagonalFactorIso B).inv = 𝟙 B :=
  (Dom.diagonalFactorIso B).hom_inv_id

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C) :
    (Dom.diagonalFactorIso B).inv ≫ (Dom.diagonalFactorIso B).hom
      = 𝟙 (Dom.diagonalSubdomain B).toDom :=
  (Dom.diagonalFactorIso B).inv_hom_id

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] (B : Dom C),
    (Dom.diagonalSubdomain B).inclusion ≫ Dom.binaryProductFst B B
      = (Dom.diagonalSubdomain B).inclusion ≫ Dom.binaryProductSnd B B :=
  @Dom.diagonalSubdomain_fst_eq_snd

/-! ### The equalizer object -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C}, (A ⟶ B) → (A ⟶ B) → Dom.Subdomain A :=
  @Dom.equalizerSubdomain

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C} (f g : A ⟶ B) :
    Dom.equalizerSubdomain f g
      = (Dom.diagonalSubdomain B).inverseImage (Dom.binaryProductLift f g) :=
  rfl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C}, (A ⟶ B) → (A ⟶ B) → Dom C :=
  @Dom.equalizerObject

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C} (f g : A ⟶ B) :
    Dom.equalizerObject f g = (Dom.equalizerSubdomain f g).toDom :=
  rfl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C} (f g : A ⟶ B), Dom.equalizerObject f g ⟶ A :=
  @Dom.equalizerInclusion

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C} (f g : A ⟶ B) :
    Dom.equalizerInclusion f g = (Dom.equalizerSubdomain f g).inclusion :=
  rfl

/-! ### Commutativity -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C} (f g : A ⟶ B),
    Dom.equalizerInclusion f g ≫ f = Dom.equalizerInclusion f g ≫ g :=
  @Dom.equalizer_comm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B : Dom C} (f g : A ⟶ B) :
    Dom.equalizerInclusion f g ≫ f = Dom.equalizerInclusion f g ≫ g :=
  Dom.equalizer_comm f g

/-! ### The lift, its uniqueness, and the universal property -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A),
    h ≫ f = h ≫ g → (W ⟶ Dom.equalizerObject f g) :=
  @Dom.equalizerLift

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g),
    Dom.equalizerLift f g h hfg ≫ Dom.equalizerInclusion f g = h :=
  @Dom.equalizerLift_inclusion

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) :
    Dom.equalizerLift f g h hfg ≫ Dom.equalizerInclusion f g = h :=
  Dom.equalizerLift_inclusion f g h hfg

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) (l : W ⟶ Dom.equalizerObject f g),
    l ≫ Dom.equalizerInclusion f g = h → l = Dom.equalizerLift f g h hfg :=
  @Dom.equalizerLift_unique

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) (l : W ⟶ Dom.equalizerObject f g)
    (hl : l ≫ Dom.equalizerInclusion f g = h) :
    l = Dom.equalizerLift f g h hfg :=
  Dom.equalizerLift_unique f g h hfg l hl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A),
    h ≫ f = h ≫ g →
    ∃! l : W ⟶ Dom.equalizerObject f g,
      l ≫ Dom.equalizerInclusion f g = h :=
  @Dom.equalizer_existsUnique

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) :
    ∃! l : W ⟶ Dom.equalizerObject f g,
      l ≫ Dom.equalizerInclusion f g = h :=
  Dom.equalizer_existsUnique f g h hfg

/-! ### The universal property, used -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) :
    ∃ l : W ⟶ Dom.equalizerObject f g,
      l ≫ Dom.equalizerInclusion f g = h ∧
        Dom.equalizerInclusion f g ≫ f = Dom.equalizerInclusion f g ≫ g ∧
        ∀ k : W ⟶ Dom.equalizerObject f g,
          k ≫ Dom.equalizerInclusion f g = h → k = l := by
  obtain ⟨l, hl, hu⟩ := Dom.equalizer_existsUnique f g h hfg
  exact ⟨l, hl, Dom.equalizer_comm f g, hu⟩

end CategoryTheory
