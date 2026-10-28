/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Domains

/-!
# Binary products in `Dom C`

The binary-product clause of Rosolini, Theorem 2.3.3. For `d e : Dom C` the
product is carried by `nearProd d.base e.base` with idempotent
`nearProd_map d.idem e.idem`, a restriction idempotent by
`PCategory.rst_nearProd_map`.

The projections are `nearProd_map d.idem e.idem ≫ p0 d.base e.base` and
`nearProd_map d.idem e.idem ≫ p1 d.base e.base`. The bare projections do not
serve: `rst (p0 X Y) = 𝟙 (nearProd X Y)`, so `p0` is a morphism out of the total
object on `nearProd X Y`, not out of the product domain.

The mediating morphism for `u : a ⟶ d` and `v : a ⟶ e` is
`partialPairing u.hom v.hom`, whose restriction is
`rst u.hom ≫ rst v.hom = a.idem`. Uniqueness is
`PCategory.eq_partialPairing_of_proj`, which carries no totality hypothesis;
`PCategory.existsUnique_partialPairing` does not apply, since a morphism out of
`a` has restriction `a.idem` rather than `𝟙 a.base`.

`Dom.binaryProduct_existsUnique` states the universal property directly; no
Mathlib limit instance is declared.

Together with the equalizers of `PCats.DomEqualizers`, this construction
yields the arbitrary pullbacks formalized in `PCats.DomPullbacks`.

The construction assumes `Category`, `PCategoryStruct`, and `PCategory`.
Ranges, zero morphisms, and choice are not used. The source-isomorphism-saturated
family of morphisms over a fixed codomain is `Dom.subdomainMorphisms` of
`PCats.DomSubdomainMorphisms`, which contains the identities, is closed under
composition, and has a pullback representative along an arbitrary morphism.
Together with the direct binary products constructed here, these results
establish Rosolini's dominion conditions for `Dom.subdomainMorphisms`. No
bundled Lean definition or structure for dominions is provided. Rosolini's
embedding of `C` into a partial-map category over `Dom C` remains
unformalized. Theorem 2.3.2 is formalized in `PCats.DomTotalEmbedding`, where
the near product of this module carries binary products in the total
subcategory and `Dom.totalEmbedding_binaryProduct_existsUnique` states their
preservation against an arbitrary apex of `Dom C`. The equalizer clause of
Corollary 2.4.10 is formalized in `PCats.DomEqualizers`, which uses the
diagonal `binaryProductLift (𝟙 B) (𝟙 B)` of this module; the finite-limit
consequence of that corollary is not bundled as a Lean result, and no
`Limits.HasEqualizers` and no finite-limit instance is declared.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

namespace Dom

/-! ### The product domain -/

/-- The product of two domains, on the near product of their bases. -/
def binaryProduct (d e : Dom C) : Dom C where
  base := nearProd d.base e.base
  idem := nearProd_map d.idem e.idem
  rst_idem := by rw [PCategory.rst_nearProd_map, d.rst_idem, e.rst_idem]

@[simp] lemma binaryProduct_base (d e : Dom C) :
    (binaryProduct d e).base = nearProd d.base e.base := rfl

@[simp] lemma binaryProduct_idem (d e : Dom C) :
    (binaryProduct d e).idem = nearProd_map d.idem e.idem := rfl

/-! ### The projections -/

/-- The first projection, restricted to the product domain. -/
def binaryProductFst (d e : Dom C) : binaryProduct d e ⟶ d where
  hom := nearProd_map d.idem e.idem ≫ p0 d.base e.base
  rst_hom := by
    change rst (nearProd_map d.idem e.idem ≫ p0 d.base e.base)
      = nearProd_map d.idem e.idem
    rw [PCategory.rst_comp_of_isTotal' _ (PCategory.p0_isTotal d.base e.base),
      PCategory.rst_nearProd_map, d.rst_idem, e.rst_idem]
  comp_idem := by
    change (nearProd_map d.idem e.idem ≫ p0 d.base e.base) ≫ d.idem
      = nearProd_map d.idem e.idem ≫ p0 d.base e.base
    rw [Category.assoc, ← PCategory.p0_nat d.idem, ← Category.assoc,
      PCategory.nearProd_comp, d.idem_comp_idem, Category.comp_id]

@[simp] lemma binaryProductFst_hom (d e : Dom C) :
    (binaryProductFst d e).hom
      = nearProd_map d.idem e.idem ≫ p0 d.base e.base := rfl

/-- The second projection, restricted to the product domain. -/
def binaryProductSnd (d e : Dom C) : binaryProduct d e ⟶ e where
  hom := nearProd_map d.idem e.idem ≫ p1 d.base e.base
  rst_hom := by
    change rst (nearProd_map d.idem e.idem ≫ p1 d.base e.base)
      = nearProd_map d.idem e.idem
    rw [PCategory.rst_comp_of_isTotal' _ (PCategory.p1_isTotal d.base e.base),
      PCategory.rst_nearProd_map, d.rst_idem, e.rst_idem]
  comp_idem := by
    change (nearProd_map d.idem e.idem ≫ p1 d.base e.base) ≫ e.idem
      = nearProd_map d.idem e.idem ≫ p1 d.base e.base
    rw [Category.assoc, ← PCategory.p1_nat e.idem, ← Category.assoc,
      PCategory.nearProd_comp, Category.comp_id, e.idem_comp_idem]

@[simp] lemma binaryProductSnd_hom (d e : Dom C) :
    (binaryProductSnd d e).hom
      = nearProd_map d.idem e.idem ≫ p1 d.base e.base := rfl

/-! ### The universal property -/

/-- The mediating morphism, the partial pairing of the two components. -/
def binaryProductLift {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    a ⟶ binaryProduct d e where
  hom := partialPairing u.hom v.hom
  rst_hom := by
    change rst (partialPairing u.hom v.hom) = a.idem
    rw [PCategory.rst_partialPairing, u.rst_hom, v.rst_hom, a.idem_comp_idem]
  comp_idem := by
    change partialPairing u.hom v.hom ≫ nearProd_map d.idem e.idem
      = partialPairing u.hom v.hom
    rw [PCategory.partialPairing_comp_nearProd_map, u.comp_idem, v.comp_idem]

@[simp] lemma binaryProductLift_hom {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    (binaryProductLift u v).hom = partialPairing u.hom v.hom := rfl

lemma binaryProductLift_fst {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    binaryProductLift u v ≫ binaryProductFst d e = u := by
  refine Hom.ext' ?_
  change partialPairing u.hom v.hom
      ≫ (nearProd_map d.idem e.idem ≫ p0 d.base e.base) = u.hom
  rw [← Category.assoc, PCategory.partialPairing_comp_nearProd_map,
    u.comp_idem, v.comp_idem, PCategory.p0_partialPairing, v.rst_hom]
  have h : rst u.hom ≫ u.hom = u.hom := RestrictionCategory.rst_comp_self u.hom
  rwa [u.rst_hom] at h

lemma binaryProductLift_snd {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    binaryProductLift u v ≫ binaryProductSnd d e = v := by
  refine Hom.ext' ?_
  change partialPairing u.hom v.hom
      ≫ (nearProd_map d.idem e.idem ≫ p1 d.base e.base) = v.hom
  rw [← Category.assoc, PCategory.partialPairing_comp_nearProd_map,
    u.comp_idem, v.comp_idem, PCategory.p1_partialPairing, u.rst_hom]
  have h : rst v.hom ≫ v.hom = v.hom := RestrictionCategory.rst_comp_self v.hom
  rwa [v.rst_hom] at h

lemma binaryProductLift_unique {a d e : Dom C} {u : a ⟶ d} {v : a ⟶ e}
    (m : a ⟶ binaryProduct d e) (hu : m ≫ binaryProductFst d e = u)
    (hv : m ≫ binaryProductSnd d e = v) : m = binaryProductLift u v := by
  refine Hom.ext' ?_
  have hmi : (m.hom : a.base ⟶ nearProd d.base e.base)
      ≫ nearProd_map d.idem e.idem = m.hom := m.comp_idem
  have hu' : (m.hom : a.base ⟶ nearProd d.base e.base)
      ≫ (nearProd_map d.idem e.idem ≫ p0 d.base e.base) = u.hom :=
    congrArg Hom.hom hu
  have hv' : (m.hom : a.base ⟶ nearProd d.base e.base)
      ≫ (nearProd_map d.idem e.idem ≫ p1 d.base e.base) = v.hom :=
    congrArg Hom.hom hv
  have h0 : (m.hom : a.base ⟶ nearProd d.base e.base) ≫ p0 d.base e.base
      = u.hom :=
    calc (m.hom : a.base ⟶ nearProd d.base e.base) ≫ p0 d.base e.base
        = (m.hom ≫ nearProd_map d.idem e.idem) ≫ p0 d.base e.base :=
          congrArg (fun t => t ≫ p0 d.base e.base) hmi.symm
      _ = m.hom ≫ (nearProd_map d.idem e.idem ≫ p0 d.base e.base) :=
          Category.assoc _ _ _
      _ = u.hom := hu'
  have h1 : (m.hom : a.base ⟶ nearProd d.base e.base) ≫ p1 d.base e.base
      = v.hom :=
    calc (m.hom : a.base ⟶ nearProd d.base e.base) ≫ p1 d.base e.base
        = (m.hom ≫ nearProd_map d.idem e.idem) ≫ p1 d.base e.base :=
          congrArg (fun t => t ≫ p1 d.base e.base) hmi.symm
      _ = m.hom ≫ (nearProd_map d.idem e.idem ≫ p1 d.base e.base) :=
          Category.assoc _ _ _
      _ = v.hom := hv'
  exact PCategory.eq_partialPairing_of_proj h0 h1

/-- The universal property: every pair of morphisms out of `a` factors uniquely
through the product. -/
theorem binaryProduct_existsUnique {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    ∃! l : a ⟶ binaryProduct d e,
      l ≫ binaryProductFst d e = u ∧ l ≫ binaryProductSnd d e = v :=
  ⟨binaryProductLift u v,
    ⟨binaryProductLift_fst u v, binaryProductLift_snd u v⟩,
    fun _ hm => binaryProductLift_unique _ hm.1 hm.2⟩

end Dom

end CategoryTheory
