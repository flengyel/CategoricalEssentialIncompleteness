/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEnumeration
public import CategoricalEssentialIncompleteness.NumericalProducts
public import PCats.Recursion

/-!
# Isomorphisms between numerical objects

The increasing enumeration and counting function give inverse total arrows
between `ℕ` and any numerical object. Restricting the counting function to its
source carrier is essential for equality with the categorical identity.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory

namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- The total arrow given by the increasing enumeration of a numerical object. -/
def enumerationArrow (X : Numerical) : totalObject nat ⟶ totalObject X :=
  totalFromFunction (enumerate X) (enumerate_computable X)
    (fun n _ => enumerate_mem X n)

/-- The total arrow given by counting, restricted to the numerical source. -/
def rankArrow (X : Numerical) : totalObject X ⟶ totalObject nat :=
  totalFromFunction (rank X) (rank_computable X) (fun _ _ => Set.mem_univ _)

@[simp] theorem mem_enumerationArrow (X : Numerical) (n m : ℕ) :
    m ∈ (enumerationArrow X).hom.val n ↔ enumerate X n = m := by
  change m ∈ (supportIdentity Set.univ n).bind (fun k => Part.some (enumerate X k)) ↔ _
  simp [Part.mem_bind_iff, eq_comm]

@[simp] theorem mem_rankArrow (X : Numerical) (n m : ℕ) :
    m ∈ (rankArrow X).hom.val n ↔ n ∈ X.carrier ∧ rank X n = m := by
  change m ∈ (supportIdentity X.carrier n).bind (fun k => Part.some (rank X k)) ↔ _
  simp [Part.mem_bind_iff, eq_comm]

@[simp] theorem enumerationArrow_rankArrow (X : Numerical) :
    (enumerationArrow X).hom ≫ (rankArrow X).hom = 𝟙 nat := by
  apply Hom.ext
  funext n
  apply Part.ext
  intro m
  simp only [comp_val, Part.mem_bind_iff, mem_enumerationArrow, mem_rankArrow,
    id_val, mem_supportIdentity]
  constructor
  · rintro ⟨k, rfl, _, h⟩
    exact ⟨Set.mem_univ _, h.symm.trans (rank_enumerate X n)⟩
  · rintro ⟨_, hm⟩
    subst m
    exact ⟨enumerate X n, rfl, enumerate_mem X n, rank_enumerate X n⟩

@[simp] theorem rankArrow_enumerationArrow (X : Numerical) :
    (rankArrow X).hom ≫ (enumerationArrow X).hom = 𝟙 X := by
  apply Hom.ext
  funext n
  apply Part.ext
  intro m
  simp only [comp_val, Part.mem_bind_iff, mem_rankArrow, mem_enumerationArrow,
    id_val, mem_supportIdentity]
  constructor
  · rintro ⟨k, ⟨hn, rfl⟩, h⟩
    exact ⟨hn, h.symm.trans (enumerate_rank X hn)⟩
  · rintro ⟨hn, hm⟩
    subst m
    exact ⟨rank X n, ⟨hn, rfl⟩, enumerate_rank X hn⟩

/-- Every numerical object is isomorphic to the object of all natural numbers. -/
def natIso (X : Numerical) : nat ≅ X where
  hom := (enumerationArrow X).hom
  inv := (rankArrow X).hom
  hom_inv_id := enumerationArrow_rankArrow X
  inv_hom_id := rankArrow_enumerationArrow X

/-- The same isomorphism in the category of total numerical arrows. -/
def totalNatIso (X : Numerical) : totalObject nat ≅ totalObject X where
  hom := enumerationArrow X
  inv := rankArrow X
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    exact enumerationArrow_rankArrow X
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    exact rankArrow_enumerationArrow X

/-- Any two numerical objects are isomorphic. -/
def objectIso (X Y : Numerical) : X ≅ Y := (natIso X).symm.trans (natIso Y)

instance numericalIsotype : RecursionCategory.Isotype Numerical where
  iso X Y := ⟨objectIso X Y⟩

end Numerical
end CategoricalEssentialIncompleteness
