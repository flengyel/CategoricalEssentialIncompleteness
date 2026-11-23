/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionRanges
public import CategoricalEssentialIncompleteness.V46KaroubiRestriction

/-! # Summand domains and total morphisms in the Karoubi envelope -/

@[expose] public section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

universe v u

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

/-- For the two coproduct summands the identity is a least upper bound. -/
theorem summands_pairComplementary [CoprodStruct C] [CategoryTheory.HasCoproducts C]
    [RestrictionCoproducts C] [CategoryTheory.Limits.HasZeroMorphisms C] [RestrictionZero C]
    (Y Z : C) : PairComplementary (summand0 Y Z) (summand1 Y Z) := by
  refine ⟨summands_disjoint Y Z, ?_⟩
  intro r h₀ h₁
  change (𝟙 (coprod Y Z)) ≫ r.hom = 𝟙 _
  rw [Category.id_comp]
  apply CategoryTheory.HasCoproducts.hom_ext
  · have h := congrArg (fun k => i0 Y Z ≫ k) (Idem.le_def.mp h₀)
    simpa only [← Category.assoc, i0_summand0, Category.comp_id] using h
  · have h := congrArg (fun k => i1 Y Z ≫ k) (Idem.le_def.mp h₁)
    simpa only [← Category.assoc, i1_summand1, Category.comp_id] using h

namespace V46.KaroubiRestriction

open CategoryTheory.Idempotents

/-- The identity at a Karoubi object is its defining idempotent. -/
theorem total_iff {P Q : Karoubi C} (f : P ⟶ Q) :
    isTotal f ↔ P.p ≫ rst f.f = P.p :=
  ⟨fun h => congrArg (fun k : P ⟶ P => k.f) h, fun h => Karoubi.hom_ext _ _ h⟩

end V46.KaroubiRestriction
end CategoricalEssentialIncompleteness.LocalConnectedness
