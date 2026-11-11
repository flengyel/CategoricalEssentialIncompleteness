/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.DomProducts
public import PCats.DomSubdomains

/-!
# Equalizers in `Dom C`

The equalizer assertion of Appendix A, lines 282–286, which is Rosolini,
Corollary 2.4.10: if `C` has ranges, then `Dom C` has equalizers. The
construction is explicit and the universal property is stated directly.

The diagonal of `B` is `binaryProductDiagonal B`, the pairing of `𝟙 B` with
itself. Its underlying morphism of `C` has a range, and `diagonalSubdomain B` is
the subdomain of `binaryProduct B B` carried by that range; the range is
received by the ambient product idempotent because the diagonal itself is, by
the minimality of the range.

The diagonal factors through its range subdomain as `diagonalFactor B`, whose
underlying morphism is again the underlying diagonal. That factor is an
isomorphism, `diagonalFactorIso`: the first projection restricted to the
diagonal subdomain is a retraction, and the range calculus turns the two
computations `Δ p₀ = 1` and `rst Δ · Δ = Δ` into the other composite. Since the
diagonal has equal projections, so does the inclusion of its range subdomain,
which is `diagonalSubdomain_fst_eq_snd`.

For parallel `f g : A ⟶ B` the equalizer subdomain of `A` is the inverse image
of the diagonal subdomain along `binaryProductLift f g`, so `equalizerObject`
and `equalizerInclusion` come from the subdomain API of `PCats.DomSubdomains`.
Commutativity `equalizer_comm` is the inverse-image square followed by the two
projections, using `diagonalSubdomain_fst_eq_snd`. A morphism `h` with
`h ≫ f = h ≫ g` lifts because `h ≫ binaryProductLift f g` is the pairing of
`h ≫ f` with itself, hence factors through the diagonal; the lift, its
inclusion equation, and its uniqueness are `inverseImageLift`,
`inverseImageLift_inclusion`, and `inverseImageLift_unique`.

Together with the binary products of `PCats.DomProducts`, this construction
yields the arbitrary pullbacks formalized in `PCats.DomPullbacks`.

The construction assumes `Category`, `PCategoryStruct`, `PCategory`, and
`HasRanges`. Zero morphisms, choice, `IsRP`, and prodominical structure are not
used. The universal property is stated directly; no Mathlib limit instance is
declared. The present hypotheses do not imply the existence of a terminal
object, so the "hence all finite limits" consequence of Corollary 2.4.10 is
not bundled as a Lean result. Rosolini's induced embedding of `C` into a
partial-map category remains unformalized.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

namespace Dom

/-! ### The diagonal -/

/-- The diagonal of `B`, the pairing of the identity with itself. -/
def binaryProductDiagonal (B : Dom C) : B ⟶ binaryProduct B B :=
  binaryProductLift (𝟙 B) (𝟙 B)

@[simp] lemma binaryProductDiagonal_fst (B : Dom C) :
    binaryProductDiagonal B ≫ binaryProductFst B B = 𝟙 B :=
  binaryProductLift_fst _ _

@[simp] lemma binaryProductDiagonal_snd (B : Dom C) :
    binaryProductDiagonal B ≫ binaryProductSnd B B = 𝟙 B :=
  binaryProductLift_snd _ _

/-- The projection equations of the diagonal on underlying morphisms. -/
private lemma diagonal_hom_fst (B : Dom C) :
    (binaryProductDiagonal B).hom ≫ (binaryProductFst B B).hom = B.idem :=
  congrArg Hom.hom (binaryProductDiagonal_fst B)

private lemma diagonal_hom_snd (B : Dom C) :
    (binaryProductDiagonal B).hom ≫ (binaryProductSnd B B).hom = B.idem :=
  congrArg Hom.hom (binaryProductDiagonal_snd B)

/-- The underlying diagonal is defined on all of `B`. -/
private lemma idem_comp_diagonal_hom (B : Dom C) :
    B.idem ≫ (binaryProductDiagonal B).hom = (binaryProductDiagonal B).hom := by
  have h : rst (binaryProductDiagonal B).hom ≫ (binaryProductDiagonal B).hom
      = (binaryProductDiagonal B).hom :=
    RestrictionCategory.rst_comp_self _
  rwa [(binaryProductDiagonal B).rst_hom] at h

/-- A pairing absorbs precomposition componentwise. -/
private lemma comp_binaryProductLift {W A D E : Dom C} (h : W ⟶ A) (u : A ⟶ D)
    (v : A ⟶ E) :
    h ≫ binaryProductLift u v = binaryProductLift (h ≫ u) (h ≫ v) :=
  binaryProductLift_unique _ (by rw [Category.assoc, binaryProductLift_fst])
    (by rw [Category.assoc, binaryProductLift_snd])

/-- Precomposition with the diagonal is the pairing of a morphism with
itself. -/
private lemma comp_binaryProductDiagonal {A B : Dom C} (u : A ⟶ B) :
    u ≫ binaryProductDiagonal B = binaryProductLift u u := by
  rw [binaryProductDiagonal, comp_binaryProductLift, Category.comp_id]

section Ranges

variable [HasRanges C]

/-! ### The diagonal subdomain -/

/-- The subdomain of `binaryProduct B B` carried by the range of the underlying
diagonal. The range is received by the product idempotent because the diagonal
is, by minimality of the range. -/
def diagonalSubdomain (B : Dom C) : Subdomain (binaryProduct B B) where
  idem := HasRanges.ran (binaryProductDiagonal B).hom
  rst_idem := HasRanges.rst_ran _
  comp_idem :=
    HasRanges.ran_le_of_receives _ (binaryProductDiagonal B).comp_idem

@[simp] lemma diagonalSubdomain_idem (B : Dom C) :
    (diagonalSubdomain B).idem
      = HasRanges.ran (binaryProductDiagonal B).hom := rfl

/-- The factor of the diagonal through its range subdomain, carried by the
underlying diagonal itself. -/
def diagonalFactor (B : Dom C) : B ⟶ (diagonalSubdomain B).toDom where
  hom := (binaryProductDiagonal B).hom
  rst_hom := (binaryProductDiagonal B).rst_hom
  comp_idem := HasRanges.comp_ran _

@[simp] lemma diagonalFactor_hom (B : Dom C) :
    (diagonalFactor B).hom = (binaryProductDiagonal B).hom := rfl

/-- The factor followed by the inclusion is the diagonal. -/
theorem diagonalFactor_inclusion (B : Dom C) :
    diagonalFactor B ≫ (diagonalSubdomain B).inclusion
      = binaryProductDiagonal B :=
  Hom.ext' (HasRanges.comp_ran _)

/-- The diagonal factor is an isomorphism. The inverse is the first projection
restricted to the diagonal subdomain. -/
def diagonalFactorIso (B : Dom C) : B ≅ (diagonalSubdomain B).toDom where
  hom := diagonalFactor B
  inv := (diagonalSubdomain B).inclusion ≫ binaryProductFst B B
  hom_inv_id := by
    rw [← Category.assoc, diagonalFactor_inclusion, binaryProductDiagonal_fst]
  inv_hom_id := by
    refine Hom.ext' ?_
    have hkey := HasRanges.ran_uniq (binaryProductDiagonal B).hom
      ((binaryProductFst B B).hom ≫ (binaryProductDiagonal B).hom)
      (𝟙 (binaryProduct B B).base)
      (by rw [← Category.assoc, diagonal_hom_fst, idem_comp_diagonal_hom,
        Category.comp_id])
    change (HasRanges.ran (binaryProductDiagonal B).hom
        ≫ (binaryProductFst B B).hom) ≫ (binaryProductDiagonal B).hom
      = HasRanges.ran (binaryProductDiagonal B).hom
    rw [Category.assoc, hkey, Category.comp_id]

/-- The inclusion of the diagonal subdomain has equal projections. -/
theorem diagonalSubdomain_fst_eq_snd (B : Dom C) :
    (diagonalSubdomain B).inclusion ≫ binaryProductFst B B
      = (diagonalSubdomain B).inclusion ≫ binaryProductSnd B B := by
  refine Hom.ext' ?_
  exact HasRanges.ran_uniq (binaryProductDiagonal B).hom
    (binaryProductFst B B).hom (binaryProductSnd B B).hom
    (by rw [diagonal_hom_fst, diagonal_hom_snd])

/-! ### The equalizer -/

/-- The equalizer subdomain of `A`: the inverse image of the diagonal subdomain
along the pairing of the two arrows. -/
def equalizerSubdomain {A B : Dom C} (f g : A ⟶ B) : Subdomain A :=
  (diagonalSubdomain B).inverseImage (binaryProductLift f g)

/-- The equalizer object. -/
def equalizerObject {A B : Dom C} (f g : A ⟶ B) : Dom C :=
  (equalizerSubdomain f g).toDom

/-- The canonical inclusion of the equalizer into `A`. -/
def equalizerInclusion {A B : Dom C} (f g : A ⟶ B) : equalizerObject f g ⟶ A :=
  (equalizerSubdomain f g).inclusion

/-- Commutativity in the spelling of the subdomain API: the inverse-image
square followed by the two projections, which agree on the diagonal
subdomain. -/
private lemma inverseImage_diagonal_comm {A B : Dom C} (f g : A ⟶ B) :
    ((diagonalSubdomain B).inverseImage (binaryProductLift f g)).inclusion ≫ f
      = ((diagonalSubdomain B).inverseImage (binaryProductLift f g)).inclusion
          ≫ g := by
  have hsq := (diagonalSubdomain B).inverseImage_comm (binaryProductLift f g)
  have hf : ((diagonalSubdomain B).inverseImage
          (binaryProductLift f g)).inclusion ≫ f
      = (diagonalSubdomain B).inverseImageMap (binaryProductLift f g)
        ≫ ((diagonalSubdomain B).inclusion ≫ binaryProductFst B B) := by
    rw [← Category.assoc, hsq, Category.assoc, binaryProductLift_fst]
  have hg : ((diagonalSubdomain B).inverseImage
          (binaryProductLift f g)).inclusion ≫ g
      = (diagonalSubdomain B).inverseImageMap (binaryProductLift f g)
        ≫ ((diagonalSubdomain B).inclusion ≫ binaryProductSnd B B) := by
    rw [← Category.assoc, hsq, Category.assoc, binaryProductLift_snd]
  rw [hf, hg, diagonalSubdomain_fst_eq_snd]

/-- The equalizer inclusion equalizes the two arrows. -/
theorem equalizer_comm {A B : Dom C} (f g : A ⟶ B) :
    equalizerInclusion f g ≫ f = equalizerInclusion f g ≫ g :=
  inverseImage_diagonal_comm f g

/-- The compatibility equation for the equalizer lift: a morphism equalizing
`f` and `g` pairs with itself, hence factors through the diagonal. -/
lemma equalizerLift_comm {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) :
    ((h ≫ f) ≫ diagonalFactor B) ≫ (diagonalSubdomain B).inclusion
      = h ≫ binaryProductLift f g := by
  rw [Category.assoc (h ≫ f), diagonalFactor_inclusion,
    comp_binaryProductDiagonal, comp_binaryProductLift, hfg]

/-- The lift of a morphism equalizing `f` and `g`. -/
def equalizerLift {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) : W ⟶ equalizerObject f g :=
  (diagonalSubdomain B).inverseImageLift (binaryProductLift f g)
    ((h ≫ f) ≫ diagonalFactor B) h (equalizerLift_comm f g h hfg)

/-- The lift factors `h` through the equalizer inclusion. -/
theorem equalizerLift_inclusion {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) :
    equalizerLift f g h hfg ≫ equalizerInclusion f g = h :=
  (diagonalSubdomain B).inverseImageLift_inclusion (binaryProductLift f g)
    ((h ≫ f) ≫ diagonalFactor B) h (equalizerLift_comm f g h hfg)

/-- The lift is the only such factorization. -/
theorem equalizerLift_unique {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) (l : W ⟶ equalizerObject f g)
    (hl : l ≫ equalizerInclusion f g = h) : l = equalizerLift f g h hfg :=
  (diagonalSubdomain B).inverseImageLift_unique (binaryProductLift f g)
    ((h ≫ f) ≫ diagonalFactor B) h (equalizerLift_comm f g h hfg) l hl

/-- The equalizer universal property, stated directly. -/
theorem equalizer_existsUnique {A B W : Dom C} (f g : A ⟶ B) (h : W ⟶ A)
    (hfg : h ≫ f = h ≫ g) :
    ∃! l : W ⟶ equalizerObject f g, l ≫ equalizerInclusion f g = h :=
  ⟨equalizerLift f g h hfg, equalizerLift_inclusion f g h hfg,
    fun l hl => equalizerLift_unique f g h hfg l hl⟩

end Ranges

end Dom

end CategoryTheory
