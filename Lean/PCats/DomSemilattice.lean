/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Recursion

/-!
# The domains on an object

Appendix A, lines 117–119: the domains on `X` form a commutative meet-semilattice
under composition, with order `d ≤ e` iff `ed = d`.

`DomSemilattice X` is the type of restriction idempotents on a fixed object `X`,
ordered by `d ≤ e` iff `ed = d`. It is not `Dom C`, whose objects are
idempotents on varying objects and whose morphisms are morphisms of `C`; here
the order is the only structure. The name says semilattice, not lattice: the
join `d₀ ∨ d₁ = ran[d₀, d₁]` needs ranges and binary coproducts and is not
defined in this module.

The `PartialOrder` instance is supplied. The meet is `meet`, with `meet_le_left`,
`meet_le_right`, `le_meet` proved separately rather than packaged as a
`SemilatticeInf` instance; packaging is a follow-up, and the three lemmas are
the content.

`top` is `1_X` and needs nothing. `bot` is `rst 0`, which equals `0`, but the
proof needs zero-absorption and not merely the existence of zero morphisms:
`⟨1, 0⟩ = Δ(1 ⊠ 0) = Δ0 = 0`, whose middle step is `Prodominical`. Both `bot`
and `rst_zero` are therefore in a section assuming it.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- A domain on `X`: a restriction idempotent `X ⟶ X`. -/
structure DomSemilattice (X : C) where
  /-- The underlying endomorphism. -/
  hom : X ⟶ X
  /-- It is a restriction idempotent. -/
  isDomain : rst hom = hom

namespace DomSemilattice

variable {X : C}

omit [PCategory C] in
lemma ext' : ∀ {d e : DomSemilattice X}, d.hom = e.hom → d = e
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- Domains are idempotent. -/
lemma idem (d : DomSemilattice X) : d.hom ≫ d.hom = d.hom := by
  have h : rst d.hom ≫ rst d.hom = rst d.hom :=
    RestrictionCategory.rst_idem d.hom
  rwa [d.isDomain] at h

/-- Domains commute, so composition is a meet rather than merely a product. -/
lemma comm (d e : DomSemilattice X) : d.hom ≫ e.hom = e.hom ≫ d.hom := by
  have h := PCategory.rst_comm' d.hom e.hom
  rwa [d.isDomain, e.isDomain] at h

/-- Domains may be interchanged before a common postcomposition. -/
lemma comm_comp {R : C} (d e : DomSemilattice X) (g : X ⟶ R) :
    d.hom ≫ e.hom ≫ g = e.hom ≫ d.hom ≫ g := by
  rw [← Category.assoc, comm d e, Category.assoc]

/-- The composite of two domains is a domain. -/
lemma isDomain_comp (d e : DomSemilattice X) : rst (d.hom ≫ e.hom) = d.hom ≫ e.hom := by
  have h := PCategory.rst_comp_rst' d.hom e.hom
  rwa [d.isDomain, e.isDomain] at h

/-- The meet of two domains is their composite. -/
def meet (d e : DomSemilattice X) : DomSemilattice X := ⟨d.hom ≫ e.hom, isDomain_comp d e⟩

@[simp] lemma meet_hom (d e : DomSemilattice X) : (meet d e).hom = d.hom ≫ e.hom := rfl

/-- The identity domain. -/
def top (X : C) : DomSemilattice X := ⟨𝟙 X, PCategory.rst_id X⟩

@[simp] lemma top_hom (X : C) : (top X).hom = 𝟙 X := rfl

instance : PartialOrder (DomSemilattice X) where
  le d e := d.hom ≫ e.hom = d.hom
  le_refl d := d.idem
  le_trans a b c hab hbc := by
    show a.hom ≫ c.hom = a.hom
    calc a.hom ≫ c.hom = (a.hom ≫ b.hom) ≫ c.hom := by rw [hab]
      _ = a.hom ≫ b.hom ≫ c.hom := Category.assoc _ _ _
      _ = a.hom ≫ b.hom := by rw [hbc]
      _ = a.hom := hab
  le_antisymm a b hab hba := ext' <| by
    calc a.hom = a.hom ≫ b.hom := hab.symm
      _ = b.hom ≫ a.hom := comm a b
      _ = b.hom := hba

lemma le_def {d e : DomSemilattice X} : d ≤ e ↔ d.hom ≫ e.hom = d.hom := Iff.rfl

lemma meet_le_left (d e : DomSemilattice X) : meet d e ≤ d := by
  change (d.hom ≫ e.hom) ≫ d.hom = d.hom ≫ e.hom
  rw [Category.assoc, comm e d, ← Category.assoc, d.idem]

lemma meet_le_right (d e : DomSemilattice X) : meet d e ≤ e := by
  change (d.hom ≫ e.hom) ≫ e.hom = d.hom ≫ e.hom
  rw [Category.assoc, e.idem]

lemma le_meet {a d e : DomSemilattice X} (h1 : a ≤ d) (h2 : a ≤ e) : a ≤ meet d e := by
  change a.hom ≫ d.hom ≫ e.hom = a.hom
  rw [← Category.assoc, h1, h2]

lemma le_top (d : DomSemilattice X) : d ≤ top X := by
  change d.hom ≫ 𝟙 X = d.hom
  rw [Category.comp_id]

/-! ### The bottom domain

In a prodominical `P`-category the zero morphism is the least element of
`Dom(X)`. Heller p. 1261 records `0_{X,X} = dom 0_{X,X}` as the smallest element
of `Dom X`. The converse is not proved here. -/

section Zero

variable [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]

omit [PCategory C] in
/-- The zero morphism is its own restriction. Stated between distinct objects:
`f ≫ 0` is a zero morphism `P ⟶ Q`, and its restriction is what the
inverse-image calculus needs. -/
lemma rst_zero (X Y : C) : rst (0 : X ⟶ Y) = 0 := by
  rw [PCategory.rst_eq_partialPairing]
  dsimp [partialPairing]
  rw [RecursionCategory.Prodominical.nearProd_zero_right]
  simp

/-- The zero domain, least in `Dom(X)`. -/
def bot (X : C) : DomSemilattice X := ⟨0, rst_zero X X⟩

omit [PCategory C] in
@[simp] lemma bot_hom (X : C) : (bot X : DomSemilattice X).hom = 0 := rfl

lemma bot_le (d : DomSemilattice X) : bot X ≤ d := by
  change (0 : X ⟶ X) ≫ d.hom = 0
  simp

end Zero

end DomSemilattice

end CategoryTheory
