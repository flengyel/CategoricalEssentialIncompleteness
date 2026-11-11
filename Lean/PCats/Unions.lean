/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.DomSemilattice

/-!
# Unions of countable families of domains

Heller's stable unions, as the manuscript states them: a domain `d` is a union
of `(dₙ)` when every `dₙ` lies below `d` and any two morphisms agreeing after
every `dₙ` agree after `d`; the union is stable when `1_W ⊠ d` is the union of
`(1_W ⊠ dₙ)` for every `W`.

Both conditions live in a plain `P`-category. Nothing here needs ranges,
coproducts, or an `ℕ`-ary coproduct: those enter only when a union is
*constructed*, which is what an `rPΣ`-category supplies and what this module
does not.

`IsUnion.le_of_forall_le` is the manuscript's "stable union below a domain",
which despite the name uses only `IsUnion`, not stability. Uniqueness of unions
follows from it and is not stated separately in the manuscript.

The second clause is the same shape as the third clause of the range axioms:
agreement after the parts forces agreement after the whole. That is why
`le_of_forall_le` and `HasRanges.ran_le_of_receives` have the same proof —
instantiate at `β' = 1`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

namespace DomSemilattice

variable {Q : C}

/-- `d` is a union of the family `dn`. -/
structure IsUnion (d : DomSemilattice Q) (dn : ℕ → DomSemilattice Q) : Prop where
  /-- Every member lies below `d`. -/
  le : ∀ n, dn n ≤ d
  /-- Morphisms agreeing after every `dₙ` agree after `d`. -/
  uniq : ∀ {R : C} (β β' : Q ⟶ R),
    (∀ n, (dn n).hom ≫ β = (dn n).hom ≫ β') → d.hom ≫ β = d.hom ≫ β'

/-- A union is below any domain above every member. -/
theorem IsUnion.le_of_forall_le {d : DomSemilattice Q} {dn : ℕ → DomSemilattice Q}
    {s : DomSemilattice Q} (h : IsUnion d dn) (hs : ∀ n, dn n ≤ s) : d ≤ s := by
  have hx := h.uniq s.hom (𝟙 Q) fun n => by
    rw [Category.comp_id]; exact hs n
  rwa [Category.comp_id] at hx

/-- A family has at most one union. -/
theorem IsUnion.unique {d d' : DomSemilattice Q} {dn : ℕ → DomSemilattice Q}
    (h : IsUnion d dn) (h' : IsUnion d' dn) : d = d' :=
  le_antisymm (h.le_of_forall_le h'.le) (h'.le_of_forall_le h.le)

/-- `1_W ⊠ d` as a domain on `W ⊠ Q`. -/
def leftTimes (d : DomSemilattice Q) (W : C) : DomSemilattice (nearProd W Q) :=
  ⟨nearProd_map (𝟙 W) d.hom, by
    rw [PCategory.rst_nearProd_map, PCategory.rst_id, d.isDomain]⟩

/-- `d ⊠ 1_W` as a domain on `Q ⊠ W`. -/
def rightTimes (d : DomSemilattice Q) (W : C) : DomSemilattice (nearProd Q W) :=
  ⟨nearProd_map d.hom (𝟙 W), by
    rw [PCategory.rst_nearProd_map, d.isDomain, PCategory.rst_id]⟩

@[simp] lemma rightTimes_hom (d : DomSemilattice Q) (W : C) :
    (d.rightTimes W).hom = nearProd_map d.hom (𝟙 W) := rfl

@[simp] lemma leftTimes_hom (d : DomSemilattice Q) (W : C) :
    (d.leftTimes W).hom = nearProd_map (𝟙 W) d.hom := rfl

/-- The union is stable when it is preserved by `1_W ⊠ -` for every `W`. -/
structure IsStableUnion (d : DomSemilattice Q) (dn : ℕ → DomSemilattice Q) :
    Prop where
  /-- `d` is a union of `dn`. -/
  isUnion : IsUnion d dn
  /-- and remains one after `1_W ⊠ -`. -/
  stable : ∀ W : C, IsUnion (d.leftTimes W) fun n => (dn n).leftTimes W

theorem IsStableUnion.unique {d d' : DomSemilattice Q} {dn : ℕ → DomSemilattice Q}
    (h : IsStableUnion d dn) (h' : IsStableUnion d' dn) : d = d' :=
  h.isUnion.unique h'.isUnion

end DomSemilattice

end CategoryTheory
