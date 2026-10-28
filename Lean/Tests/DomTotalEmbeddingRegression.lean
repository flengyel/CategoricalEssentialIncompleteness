/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.DomTotalEmbedding

/-!
# Signature guards for the total-object embedding

Each `example` fails to elaborate if a protected signature or equation changes.
Exact `@`-ascriptions pin the telescopes of
`RestrictionCategory.TotalSubcategory` and its binary-product API,
`Dom.totalEmbedding` with its object and map equations,
`Dom.totalEmbedding_full`, `Dom.totalEmbedding_faithful`,
`Dom.totalEmbeddingFullyFaithful`, the mapped-product lift with its two
projection equations and its uniqueness, and
`Dom.totalEmbedding_binaryProduct_existsUnique` with an arbitrary apex
`A : Dom C`.

Each guard writes out the whole telescope, so it fails to elaborate if a range,
`IsRP`, zero-morphism, choice, dominical, prodominical, isotype, recursion, or
limits hypothesis enters a protected declaration. Classical axiom dependencies
are not visible to these guards and are checked separately by
`check_axioms.lean`.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

#check @RestrictionCategory.TotalSubcategory
#check @RestrictionCategory.TotalSubcategory.binaryProduct
#check @RestrictionCategory.TotalSubcategory.binaryProduct_obj
#check @RestrictionCategory.TotalSubcategory.binaryProductFst
#check @RestrictionCategory.TotalSubcategory.binaryProductFst_hom
#check @RestrictionCategory.TotalSubcategory.binaryProductSnd
#check @RestrictionCategory.TotalSubcategory.binaryProductSnd_hom
#check @RestrictionCategory.TotalSubcategory.binaryProductLift
#check @RestrictionCategory.TotalSubcategory.binaryProductLift_hom
#check @RestrictionCategory.TotalSubcategory.binaryProductLift_fst
#check @RestrictionCategory.TotalSubcategory.binaryProductLift_snd
#check @RestrictionCategory.TotalSubcategory.binaryProductLift_unique
#check @RestrictionCategory.TotalSubcategory.binaryProduct_existsUnique
#check @Dom.totalEmbedding
#check @Dom.totalEmbedding_obj
#check @Dom.totalEmbedding_map_hom
#check @Dom.totalEmbedding_full
#check @Dom.totalEmbedding_faithful
#check @Dom.totalEmbeddingFullyFaithful
#check @Dom.totalEmbeddingBinaryProductLift
#check @Dom.totalEmbeddingBinaryProductLift_hom
#check @Dom.totalEmbeddingBinaryProductLift_fst
#check @Dom.totalEmbeddingBinaryProductLift_snd
#check @Dom.totalEmbeddingBinaryProductLift_unique
#check @Dom.totalEmbedding_binaryProduct_existsUnique

/-! ### The total subcategory -/

example : ∀ (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C],
    Type u :=
  @RestrictionCategory.TotalSubcategory

example (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C] :
    RestrictionCategory.TotalSubcategory C
      = WideSubcategory (RestrictionCategory.isTotal (C := C)) :=
  rfl

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} (f : X ⟶ Y) :
    RestrictionCategory.isTotal f.hom :=
  f.property

/-! ### Binary products in the total subcategory -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    RestrictionCategory.TotalSubcategory C →
      RestrictionCategory.TotalSubcategory C →
        RestrictionCategory.TotalSubcategory C :=
  @RestrictionCategory.TotalSubcategory.binaryProduct

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C),
    (RestrictionCategory.TotalSubcategory.binaryProduct X Y).obj
      = PCategoryStruct.nearProd X.obj Y.obj :=
  @RestrictionCategory.TotalSubcategory.binaryProduct_obj

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C) :
    (RestrictionCategory.TotalSubcategory.binaryProduct X Y).obj
      = PCategoryStruct.nearProd X.obj Y.obj :=
  RestrictionCategory.TotalSubcategory.binaryProduct_obj X Y

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C),
    RestrictionCategory.TotalSubcategory.binaryProduct X Y ⟶ X :=
  @RestrictionCategory.TotalSubcategory.binaryProductFst

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C),
    (RestrictionCategory.TotalSubcategory.binaryProductFst X Y).hom
      = PCategoryStruct.p0 X.obj Y.obj :=
  @RestrictionCategory.TotalSubcategory.binaryProductFst_hom

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C) :
    (RestrictionCategory.TotalSubcategory.binaryProductFst X Y).hom
      = PCategoryStruct.p0 X.obj Y.obj :=
  RestrictionCategory.TotalSubcategory.binaryProductFst_hom X Y

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C),
    RestrictionCategory.TotalSubcategory.binaryProduct X Y ⟶ Y :=
  @RestrictionCategory.TotalSubcategory.binaryProductSnd

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C),
    (RestrictionCategory.TotalSubcategory.binaryProductSnd X Y).hom
      = PCategoryStruct.p1 X.obj Y.obj :=
  @RestrictionCategory.TotalSubcategory.binaryProductSnd_hom

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X Y : RestrictionCategory.TotalSubcategory C) :
    (RestrictionCategory.TotalSubcategory.binaryProductSnd X Y).hom
      = PCategoryStruct.p1 X.obj Y.obj :=
  RestrictionCategory.TotalSubcategory.binaryProductSnd_hom X Y

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A X Y : RestrictionCategory.TotalSubcategory C}, (A ⟶ X) → (A ⟶ Y) →
    (A ⟶ RestrictionCategory.TotalSubcategory.binaryProduct X Y) :=
  @RestrictionCategory.TotalSubcategory.binaryProductLift

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A X Y : RestrictionCategory.TotalSubcategory C} (u : A ⟶ X) (v : A ⟶ Y),
    (RestrictionCategory.TotalSubcategory.binaryProductLift u v).hom
      = PCategoryStruct.partialPairing u.hom v.hom :=
  @RestrictionCategory.TotalSubcategory.binaryProductLift_hom

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A X Y : RestrictionCategory.TotalSubcategory C} (u : A ⟶ X) (v : A ⟶ Y) :
    (RestrictionCategory.TotalSubcategory.binaryProductLift u v).hom
      = PCategoryStruct.partialPairing u.hom v.hom :=
  RestrictionCategory.TotalSubcategory.binaryProductLift_hom u v

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A X Y : RestrictionCategory.TotalSubcategory C} (u : A ⟶ X) (v : A ⟶ Y),
    RestrictionCategory.TotalSubcategory.binaryProductLift u v
        ≫ RestrictionCategory.TotalSubcategory.binaryProductFst X Y = u :=
  @RestrictionCategory.TotalSubcategory.binaryProductLift_fst

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A X Y : RestrictionCategory.TotalSubcategory C} (u : A ⟶ X) (v : A ⟶ Y),
    RestrictionCategory.TotalSubcategory.binaryProductLift u v
        ≫ RestrictionCategory.TotalSubcategory.binaryProductSnd X Y = v :=
  @RestrictionCategory.TotalSubcategory.binaryProductLift_snd

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A X Y : RestrictionCategory.TotalSubcategory C} {u : A ⟶ X} {v : A ⟶ Y}
    (m : A ⟶ RestrictionCategory.TotalSubcategory.binaryProduct X Y),
    m ≫ RestrictionCategory.TotalSubcategory.binaryProductFst X Y = u →
    m ≫ RestrictionCategory.TotalSubcategory.binaryProductSnd X Y = v →
    m = RestrictionCategory.TotalSubcategory.binaryProductLift u v :=
  @RestrictionCategory.TotalSubcategory.binaryProductLift_unique

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A X Y : RestrictionCategory.TotalSubcategory C} (u : A ⟶ X) (v : A ⟶ Y),
    ∃! l : A ⟶ RestrictionCategory.TotalSubcategory.binaryProduct X Y,
      l ≫ RestrictionCategory.TotalSubcategory.binaryProductFst X Y = u ∧
      l ≫ RestrictionCategory.TotalSubcategory.binaryProductSnd X Y = v :=
  @RestrictionCategory.TotalSubcategory.binaryProduct_existsUnique

/-! ### The embedding, its object and map equations -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    RestrictionCategory.TotalSubcategory C ⥤ Dom C :=
  @Dom.totalEmbedding

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (X : RestrictionCategory.TotalSubcategory C),
    (Dom.totalEmbedding (C := C)).obj X = Dom.total X.obj :=
  @Dom.totalEmbedding_obj

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} (f : X ⟶ Y),
    ((Dom.totalEmbedding (C := C)).map f).hom = f.hom :=
  @Dom.totalEmbedding_map_hom

/-! ### Fullness and faithfulness -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    (Dom.totalEmbedding (C := C)).Full :=
  @Dom.totalEmbedding_full

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    (Dom.totalEmbedding (C := C)).Faithful :=
  @Dom.totalEmbedding_faithful

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] :
    (Dom.totalEmbedding (C := C)).Full :=
  inferInstance

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] :
    (Dom.totalEmbedding (C := C)).Faithful :=
  inferInstance

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C}
    (u : (Dom.totalEmbedding (C := C)).obj X
      ⟶ (Dom.totalEmbedding (C := C)).obj Y) :
    ∃ f : X ⟶ Y, (Dom.totalEmbedding (C := C)).map f = u :=
  Functor.Full.map_surjective u

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} (f g : X ⟶ Y)
    (h : (Dom.totalEmbedding (C := C)).map f
      = (Dom.totalEmbedding (C := C)).map g) : f = g :=
  Functor.Faithful.map_injective h

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    (Dom.totalEmbedding (C := C)).FullyFaithful :=
  @Dom.totalEmbeddingFullyFaithful

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C}
    (u : (Dom.totalEmbedding (C := C)).obj X
      ⟶ (Dom.totalEmbedding (C := C)).obj Y) :
    ((Dom.totalEmbeddingFullyFaithful (C := C)).preimage u).hom = u.hom :=
  rfl

/-! ### Preservation of binary products, at an arbitrary apex of `Dom C` -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} {A : Dom C},
    (A ⟶ (Dom.totalEmbedding (C := C)).obj X) →
    (A ⟶ (Dom.totalEmbedding (C := C)).obj Y) →
    (A ⟶ (Dom.totalEmbedding (C := C)).obj
      (RestrictionCategory.TotalSubcategory.binaryProduct X Y)) :=
  @Dom.totalEmbeddingBinaryProductLift

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (Dom.totalEmbedding (C := C)).obj X)
    (v : A ⟶ (Dom.totalEmbedding (C := C)).obj Y),
    (Dom.totalEmbeddingBinaryProductLift u v).hom
      = PCategoryStruct.partialPairing u.hom v.hom :=
  @Dom.totalEmbeddingBinaryProductLift_hom

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (Dom.totalEmbedding (C := C)).obj X)
    (v : A ⟶ (Dom.totalEmbedding (C := C)).obj Y) :
    (Dom.totalEmbeddingBinaryProductLift u v).hom
      = PCategoryStruct.partialPairing u.hom v.hom :=
  Dom.totalEmbeddingBinaryProductLift_hom u v

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (Dom.totalEmbedding (C := C)).obj X)
    (v : A ⟶ (Dom.totalEmbedding (C := C)).obj Y),
    Dom.totalEmbeddingBinaryProductLift u v ≫ (Dom.totalEmbedding (C := C)).map
        (RestrictionCategory.TotalSubcategory.binaryProductFst X Y) = u :=
  @Dom.totalEmbeddingBinaryProductLift_fst

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (Dom.totalEmbedding (C := C)).obj X)
    (v : A ⟶ (Dom.totalEmbedding (C := C)).obj Y),
    Dom.totalEmbeddingBinaryProductLift u v ≫ (Dom.totalEmbedding (C := C)).map
        (RestrictionCategory.TotalSubcategory.binaryProductSnd X Y) = v :=
  @Dom.totalEmbeddingBinaryProductLift_snd

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} {A : Dom C}
    {u : A ⟶ (Dom.totalEmbedding (C := C)).obj X}
    {v : A ⟶ (Dom.totalEmbedding (C := C)).obj Y}
    (m : A ⟶ (Dom.totalEmbedding (C := C)).obj
      (RestrictionCategory.TotalSubcategory.binaryProduct X Y)),
    m ≫ (Dom.totalEmbedding (C := C)).map
        (RestrictionCategory.TotalSubcategory.binaryProductFst X Y) = u →
    m ≫ (Dom.totalEmbedding (C := C)).map
        (RestrictionCategory.TotalSubcategory.binaryProductSnd X Y) = v →
    m = Dom.totalEmbeddingBinaryProductLift u v :=
  @Dom.totalEmbeddingBinaryProductLift_unique

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (Dom.totalEmbedding (C := C)).obj X)
    (v : A ⟶ (Dom.totalEmbedding (C := C)).obj Y),
    ∃! l : A ⟶ (Dom.totalEmbedding (C := C)).obj
        (RestrictionCategory.TotalSubcategory.binaryProduct X Y),
      l ≫ (Dom.totalEmbedding (C := C)).map
          (RestrictionCategory.TotalSubcategory.binaryProductFst X Y) = u ∧
      l ≫ (Dom.totalEmbedding (C := C)).map
          (RestrictionCategory.TotalSubcategory.binaryProductSnd X Y) = v :=
  @Dom.totalEmbedding_binaryProduct_existsUnique

/-- The apex is an arbitrary object of `Dom C`, not one in the image of the
embedding: `A` here carries an arbitrary restriction idempotent. -/
example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y : RestrictionCategory.TotalSubcategory C} (Z : C) (e : Z ⟶ Z)
    (he : PCategoryStruct.rst e = e)
    (u : (⟨Z, e, he⟩ : Dom C) ⟶ (Dom.totalEmbedding (C := C)).obj X)
    (v : (⟨Z, e, he⟩ : Dom C) ⟶ (Dom.totalEmbedding (C := C)).obj Y) :
    ∃! l : (⟨Z, e, he⟩ : Dom C) ⟶ (Dom.totalEmbedding (C := C)).obj
        (RestrictionCategory.TotalSubcategory.binaryProduct X Y),
      l ≫ (Dom.totalEmbedding (C := C)).map
          (RestrictionCategory.TotalSubcategory.binaryProductFst X Y) = u ∧
      l ≫ (Dom.totalEmbedding (C := C)).map
          (RestrictionCategory.TotalSubcategory.binaryProductSnd X Y) = v :=
  Dom.totalEmbedding_binaryProduct_existsUnique u v

end CategoryTheory
