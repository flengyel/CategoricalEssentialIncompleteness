/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.Widesubcategory
public import PCats.DomProducts

/-!
# The total-object embedding and preservation of binary products

Rosolini, Theorem 2.3.2: the wide subcategory `C_T` of total morphisms embeds
fully and faithfully into `Dom C`, and the embedding preserves binary products.

`RestrictionCategory.TotalSubcategory C` is `WideSubcategory` of the
multiplicative morphism property `RestrictionCategory.isTotal`, so its objects
are the objects of `C` and its morphisms are the total morphisms of `C`. The
near product carries binary products there: `p₀` and `p₁` are total, a partial
pairing of total morphisms is total, and the mediating morphism is unique by
`PCategory.eq_partialPairing_of_proj`. `binaryProduct_existsUnique` states that
universal property directly; no `Limits.HasBinaryProducts` instance is
declared.

`Dom.totalEmbedding` sends `X` to `Dom.total X.obj` and a total morphism to the
`Dom.Hom` with the same underlying morphism, the totality hypothesis supplying
`rst_hom` and `Category.comp_id` supplying `comp_idem`. It is faithful because
a `Dom.Hom` is determined by its underlying morphism, and full because a
morphism `Dom.total X.obj ⟶ Dom.total Y.obj` carries `rst u.hom = 𝟙 X.obj` in
its `rst_hom` field, which is exactly the totality needed to read it back as a
morphism of `C_T`. The preimage is written down; no `Functor.preimage` and no
choice principle is used.

Full faithfulness alone gives the product universal property only against
apices in the image of the embedding.
`Dom.totalEmbedding_binaryProduct_existsUnique` is stated against an arbitrary
`A : Dom C`: the mediating morphism is the partial pairing of the underlying
morphisms, its restriction is `A.idem` by `PCategory.rst_partialPairing`, and
uniqueness is again `PCategory.eq_partialPairing_of_proj`, which needs no
totality. The image object `Dom.total (X.obj ⊠ Y.obj)` and the product
`Dom.binaryProduct (Dom.total X.obj) (Dom.total Y.obj)` are not definitionally
equal, so the property is proved directly rather than transported.

The construction assumes `Category`, `PCategoryStruct`, and `PCategory`.
Ranges, `IsRP`, zero morphisms, choice, dominical, prodominical, isotype, and
recursion structure are not used, and no limits API is involved. Rosolini's
embedding of `C` into a partial-map category over `Dom C`, and a finite-limit
instance, are not formalized; the binary products of `Dom C` and the
equalizers of `PCats.DomEqualizers` do not by themselves yield Mathlib's
`HasFiniteLimits`, which also requires the empty diagram.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- The wide subcategory of total morphisms, Rosolini's `C_T`. -/
abbrev RestrictionCategory.TotalSubcategory (C : Type u) [Category.{v} C]
    [PCategoryStruct C] [PCategory C] :=
  WideSubcategory (RestrictionCategory.isTotal (C := C))

namespace RestrictionCategory.TotalSubcategory

/-! ### Binary products in the total subcategory -/

/-- The product of two objects, carried by the near product. -/
def binaryProduct (X Y : TotalSubcategory C) : TotalSubcategory C :=
  ⟨nearProd X.obj Y.obj⟩

@[simp] lemma binaryProduct_obj (X Y : TotalSubcategory C) :
    (binaryProduct X Y).obj = nearProd X.obj Y.obj := rfl

/-- The first projection, total by `PCategory.p0_isTotal`. -/
def binaryProductFst (X Y : TotalSubcategory C) : binaryProduct X Y ⟶ X :=
  ⟨p0 X.obj Y.obj, PCategory.p0_isTotal X.obj Y.obj⟩

@[simp] lemma binaryProductFst_hom (X Y : TotalSubcategory C) :
    (binaryProductFst X Y).hom = p0 X.obj Y.obj := rfl

/-- The second projection, total by `PCategory.p1_isTotal`. -/
def binaryProductSnd (X Y : TotalSubcategory C) : binaryProduct X Y ⟶ Y :=
  ⟨p1 X.obj Y.obj, PCategory.p1_isTotal X.obj Y.obj⟩

@[simp] lemma binaryProductSnd_hom (X Y : TotalSubcategory C) :
    (binaryProductSnd X Y).hom = p1 X.obj Y.obj := rfl

/-- The mediating morphism, the partial pairing of the two components. -/
def binaryProductLift {A X Y : TotalSubcategory C} (u : A ⟶ X) (v : A ⟶ Y) :
    A ⟶ binaryProduct X Y :=
  ⟨partialPairing u.hom v.hom,
    PCategory.isTotal_partialPairing u.property v.property⟩

@[simp] lemma binaryProductLift_hom {A X Y : TotalSubcategory C} (u : A ⟶ X)
    (v : A ⟶ Y) :
    (binaryProductLift u v).hom = partialPairing u.hom v.hom := rfl

theorem binaryProductLift_fst {A X Y : TotalSubcategory C} (u : A ⟶ X)
    (v : A ⟶ Y) : binaryProductLift u v ≫ binaryProductFst X Y = u :=
  WideSubcategory.hom_ext _
    (PCategory.p0_partialPairing_of_isTotal u.hom v.property)

theorem binaryProductLift_snd {A X Y : TotalSubcategory C} (u : A ⟶ X)
    (v : A ⟶ Y) : binaryProductLift u v ≫ binaryProductSnd X Y = v :=
  WideSubcategory.hom_ext _
    (PCategory.p1_partialPairing_of_isTotal v.hom u.property)

theorem binaryProductLift_unique {A X Y : TotalSubcategory C} {u : A ⟶ X}
    {v : A ⟶ Y} (m : A ⟶ binaryProduct X Y)
    (hu : m ≫ binaryProductFst X Y = u)
    (hv : m ≫ binaryProductSnd X Y = v) : m = binaryProductLift u v :=
  WideSubcategory.hom_ext _
    (PCategory.eq_partialPairing_of_proj
      (congrArg InducedWideCategory.Hom.hom hu)
      (congrArg InducedWideCategory.Hom.hom hv))

/-- The universal property of the binary product, stated directly. -/
theorem binaryProduct_existsUnique {A X Y : TotalSubcategory C} (u : A ⟶ X)
    (v : A ⟶ Y) :
    ∃! l : A ⟶ binaryProduct X Y,
      l ≫ binaryProductFst X Y = u ∧ l ≫ binaryProductSnd X Y = v :=
  ⟨binaryProductLift u v,
    ⟨binaryProductLift_fst u v, binaryProductLift_snd u v⟩,
    fun _ hm => binaryProductLift_unique _ hm.1 hm.2⟩

end RestrictionCategory.TotalSubcategory

namespace Dom

open RestrictionCategory (TotalSubcategory)

/-! ### The embedding -/

/-- The total-object embedding `C_T ⥤ Dom C`. -/
def totalEmbedding : TotalSubcategory C ⥤ Dom C where
  obj X := Dom.total X.obj
  map {_ _} f := ⟨f.hom, f.property, Category.comp_id f.hom⟩
  map_id _ := Hom.ext' rfl
  map_comp _ _ := Hom.ext' rfl

@[simp] theorem totalEmbedding_obj (X : TotalSubcategory C) :
    (totalEmbedding (C := C)).obj X = Dom.total X.obj := rfl

@[simp] theorem totalEmbedding_map_hom {X Y : TotalSubcategory C}
    (f : X ⟶ Y) : ((totalEmbedding (C := C)).map f).hom = f.hom := rfl

/-- The embedding is full: a morphism of `Dom C` between total objects carries
its own totality in `rst_hom`, so it is read back directly. -/
instance totalEmbedding_full : (totalEmbedding (C := C)).Full where
  map_surjective u := ⟨⟨u.hom, u.rst_hom⟩, Hom.ext' rfl⟩

/-- The embedding is faithful: a `Dom.Hom` is determined by its underlying
morphism. -/
instance totalEmbedding_faithful : (totalEmbedding (C := C)).Faithful where
  map_injective h := WideSubcategory.hom_ext _ (congrArg Hom.hom h)

/-- The bundled full faithfulness, with the preimage written down. -/
def totalEmbeddingFullyFaithful :
    (totalEmbedding (C := C)).FullyFaithful where
  preimage u := ⟨u.hom, u.rst_hom⟩
  map_preimage _ := Hom.ext' rfl
  preimage_map _ := WideSubcategory.hom_ext _ rfl

/-! ### Preservation of binary products

The apex is an arbitrary `A : Dom C`, not merely an object in the image of the
embedding. -/

/-- The mediating morphism from an arbitrary domain into the image of the
product. -/
def totalEmbeddingBinaryProductLift {X Y : TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (totalEmbedding (C := C)).obj X)
    (v : A ⟶ (totalEmbedding (C := C)).obj Y) :
    A ⟶ (totalEmbedding (C := C)).obj
      (TotalSubcategory.binaryProduct X Y) where
  hom := partialPairing u.hom v.hom
  rst_hom := by
    change rst (partialPairing u.hom v.hom) = A.idem
    rw [PCategory.rst_partialPairing, u.rst_hom, v.rst_hom, A.idem_comp_idem]
  comp_idem := Category.comp_id _

@[simp] theorem totalEmbeddingBinaryProductLift_hom
    {X Y : TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (totalEmbedding (C := C)).obj X)
    (v : A ⟶ (totalEmbedding (C := C)).obj Y) :
    (totalEmbeddingBinaryProductLift u v).hom
      = partialPairing u.hom v.hom := rfl

/-- The underlying first-projection equation: two morphisms with a common
restriction pair to a partial pairing that projects back to them. -/
private lemma partialPairing_p0_of_rst {A X Y : C} {a : A ⟶ A} {f : A ⟶ X}
    {g : A ⟶ Y} (hf : rst f = a) (hg : rst g = a) :
    partialPairing f g ≫ p0 X Y = f := by
  rw [PCategory.p0_partialPairing, hg, ← hf]
  exact RestrictionCategory.rst_comp_self f

private lemma partialPairing_p1_of_rst {A X Y : C} {a : A ⟶ A} {f : A ⟶ X}
    {g : A ⟶ Y} (hf : rst f = a) (hg : rst g = a) :
    partialPairing f g ≫ p1 X Y = g := by
  rw [PCategory.p1_partialPairing, hf, ← hg]
  exact RestrictionCategory.rst_comp_self g

theorem totalEmbeddingBinaryProductLift_fst {X Y : TotalSubcategory C}
    {A : Dom C} (u : A ⟶ (totalEmbedding (C := C)).obj X)
    (v : A ⟶ (totalEmbedding (C := C)).obj Y) :
    totalEmbeddingBinaryProductLift u v ≫ (totalEmbedding (C := C)).map
        (TotalSubcategory.binaryProductFst X Y) = u :=
  Hom.ext' (partialPairing_p0_of_rst u.rst_hom v.rst_hom)

theorem totalEmbeddingBinaryProductLift_snd {X Y : TotalSubcategory C}
    {A : Dom C} (u : A ⟶ (totalEmbedding (C := C)).obj X)
    (v : A ⟶ (totalEmbedding (C := C)).obj Y) :
    totalEmbeddingBinaryProductLift u v ≫ (totalEmbedding (C := C)).map
        (TotalSubcategory.binaryProductSnd X Y) = v :=
  Hom.ext' (partialPairing_p1_of_rst u.rst_hom v.rst_hom)

theorem totalEmbeddingBinaryProductLift_unique {X Y : TotalSubcategory C}
    {A : Dom C} {u : A ⟶ (totalEmbedding (C := C)).obj X}
    {v : A ⟶ (totalEmbedding (C := C)).obj Y}
    (m : A ⟶ (totalEmbedding (C := C)).obj
      (TotalSubcategory.binaryProduct X Y))
    (hu : m ≫ (totalEmbedding (C := C)).map
      (TotalSubcategory.binaryProductFst X Y) = u)
    (hv : m ≫ (totalEmbedding (C := C)).map
      (TotalSubcategory.binaryProductSnd X Y) = v) :
    m = totalEmbeddingBinaryProductLift u v :=
  Hom.ext'
    (PCategory.eq_partialPairing_of_proj (congrArg Hom.hom hu)
      (congrArg Hom.hom hv))

/-- The embedding preserves binary products, against an arbitrary apex of
`Dom C`. -/
theorem totalEmbedding_binaryProduct_existsUnique
    {X Y : TotalSubcategory C} {A : Dom C}
    (u : A ⟶ (totalEmbedding (C := C)).obj X)
    (v : A ⟶ (totalEmbedding (C := C)).obj Y) :
    ∃! l : A ⟶ (totalEmbedding (C := C)).obj
        (TotalSubcategory.binaryProduct X Y),
      l ≫ (totalEmbedding (C := C)).map
          (TotalSubcategory.binaryProductFst X Y) = u ∧
      l ≫ (totalEmbedding (C := C)).map
          (TotalSubcategory.binaryProductSnd X Y) = v :=
  ⟨totalEmbeddingBinaryProductLift u v,
    ⟨totalEmbeddingBinaryProductLift_fst u v,
      totalEmbeddingBinaryProductLift_snd u v⟩,
    fun _ hm => totalEmbeddingBinaryProductLift_unique _ hm.1 hm.2⟩

end Dom

end CategoryTheory
