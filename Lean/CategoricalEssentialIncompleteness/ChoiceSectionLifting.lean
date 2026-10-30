/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RestrictionCompatibility

/-! # Source choice as a sufficient condition for section lifting -/

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoryTheory.Limits (HasZeroMorphisms)

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R] [BinaryJoins R]
variable [HasZeroMorphisms A] [RestrictionZero A] [BinaryJoins A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A]
variable [Splits A] [JoinInverse A] [LocallyConnected A] [WeakChoice A]

omit [RestrictionZero R] [BinaryJoins R] [RestrictionZero A] [BinaryJoins A]
    [RestrictionCoproducts R] [RestrictionCoproducts A] [Splits A] [JoinInverse A]
    [LocallyConnected A] [WeakChoice A] in
/-- Mapping a source section and applying the canonical coproduct comparison
gives a section in the target. -/
theorem map_switch_section (F : RangeFunctor R A) {U : R} (c c' : Idem U)
    (ℓ : U ⟶ coprod U U) (hℓ : SectionOf (copair c'.hom c.hom) ℓ) :
    SectionOf (copair (F.mapIdem c').hom (F.mapIdem c).hom)
      (F.toFunctor.map ℓ ≫ (F.comparison U U).inv) := by
  let p := copair c'.hom c.hom
  let pA := copair (F.mapIdem c').hom (F.mapIdem c).hom
  have hcomp : (F.comparison U U).hom ≫ F.toFunctor.map p = pA :=
    F.comparison_copair c'.hom c.hom
  have hinv : (F.comparison U U).inv ≫ pA = F.toFunctor.map p := by
    rw [← hcomp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have htotal : isTotal (F.comparison U U).inv := iso_total (F.comparison U U).symm
  constructor
  · change (F.toFunctor.map ℓ ≫ (F.comparison U U).inv) ≫ pA = _
    rw [Category.assoc, hinv, ← F.toFunctor.map_comp, hℓ.comp, F.map_restrict,
      rst_comp_of_isTotal _ htotal]
  · change pA ≫ (F.toFunctor.map ℓ ≫ (F.comparison U U).inv) ≫ pA = pA
    rw [Category.assoc, hinv, ← hcomp]
    simp only [Category.assoc]
    rw [← F.toFunctor.map_comp, ← F.toFunctor.map_comp, hℓ.receives]

omit [RestrictionCoproducts R] in
/-- This sufficient condition is separate from Theorem 6.3's lifting
hypothesis. -/
theorem section_lifting_of_choice [CategoryTheory.HasChoice R]
    (F : RangeFunctor R A) (U : R) : SectionLifting F U := by
  intro c c' hc
  obtain ⟨ℓ, hℓ⟩ := CategoryTheory.HasChoice.exists_isSection (copair c'.hom c.hom)
  have hs := map_switch_section F c c' ℓ ((section_iff_existing _ _).mpr hℓ)
  have hspec := switchSection_spec (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc)
  have hp : PartialMono (copair (F.mapIdem c').hom (F.mapIdem c).hom) :=
    (local_switch (F.mapIdem c') (F.mapIdem c)
    (F.map_complementary hc).symm.disjoint).1
  have he := hp.section_unique hs hspec.1
  refine ⟨ℓ, ?_⟩
  have h := congrArg (fun k => k ≫ (F.comparison U U).hom) he
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

end CategoricalEssentialIncompleteness.LocalConnectedness
