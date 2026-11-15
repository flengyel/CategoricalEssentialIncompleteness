/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceEvaluationSubobjects
public import CategoricalEssentialIncompleteness.V46EquivalenceSubobjects
public import CategoricalEssentialIncompleteness.V46PartialMapTotals
public import CategoricalEssentialIncompleteness.V46RegularEquivalence

/-! # Inseparability in actual parameter slices and their total categories -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SliceInseparability
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
local instance (U : C) : Regular (Over U) := RegularSlices.regular U
local instance (U : C) : FinitaryExtensive (Over U) := RegularSlices.finitaryExtensive U
local instance (U : C) : PreservesFiniteLimits (constantFamilyFunctor U) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U

/-- A complementary separator in the slice gives a separator of its
underlying subobjects. Every slice subobject is covered by the order isomorphism. -/
theorem underlying_separator {U : C} {S : Over U} {A B : Subobject S}
    (hs : HasSubobjectSeparator A B) :
    HasSubobjectSeparator (SliceSubobjectPredicates.underlying A)
      (SliceSubobjectPredicates.underlying B) := by
  obtain ⟨p, ha, hb⟩ := hs
  let e := SliceSubobjectPredicates.orderIso S
  have hc : IsCompl (e p.positive) (e p.negative) := by
    constructor
    · apply disjoint_iff.mpr
      rw [← e.map_inf, p.complementary.inf_eq_bot, e.map_bot]
    · apply codisjoint_iff.mpr
      rw [← e.map_sup, p.complementary.sup_eq_top, e.map_top]
  exact ⟨⟨e p.positive, e p.negative, hc⟩, e.monotone ha, e.monotone hb⟩

/-- Evaluation excludes every complementary slice separator, not merely
those that are constant families. -/
theorem constant {Z U S : C} (point : Z ⟶ U) (hZ : IsTerminal Z)
    (ν : S ⟶ S) (A : Subobject S)
    (hi : SubobjectInseparable A ((Subobject.pullback ν).obj A)) :
    SubobjectInseparable (FiniteLimitSubobjects.object (constantFamilyFunctor U) A)
      ((Subobject.pullback ((constantFamilyFunctor U).map ν)).obj
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) A)) := by
  refine ⟨SliceSubobjectPredicates.constant_consistency U ν A hi.1, ?_⟩
  intro hs
  have h := subobject_separator_pullback (SliceSubobjectPredicates.fiber point hZ S)
    (underlying_separator hs)
  change HasSubobjectSeparator
    (SliceSubobjectPredicates.evaluate point hZ
      (FiniteLimitSubobjects.object (constantFamilyFunctor U) A))
    (SliceSubobjectPredicates.evaluate point hZ
      ((Subobject.pullback ((constantFamilyFunctor U).map ν)).obj
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) A))) at h
  rw [SliceSubobjectPredicates.evaluate_refutation,
    SliceSubobjectPredicates.evaluate_constant] at h
  exact hi.2 h

/-- An inseparable theory/refutation pair excludes a consistent complete
extension even before imposing deduction closure on that extension. -/
theorem noncoverage {S : C} (ν : S ⟶ S) (A : Subobject S)
    (hi : SubobjectInseparable A ((Subobject.pullback ν).obj A))
    (W : Subobject S) (hAW : A ≤ W)
    (hc : W ⊓ (Subobject.pullback ν).obj W = ⊥) :
    W ⊔ (Subobject.pullback ν).obj W ≠ ⊤ := by
  intro hcomplete
  apply hi.2
  refine ⟨⟨W, (Subobject.pullback ν).obj W, ?_⟩, hAW, (Subobject.pullback ν).monotone hAW⟩
  constructor
  · exact disjoint_iff.mpr hc
  · exact codisjoint_iff.mpr hcomplete

namespace PartialTotals
variable (D : Type u) [Category.{v} D] [Regular D] [FinitaryExtensive D]

local instance totalLimits : HasFiniteLimits (PartialMaps.Tot D) where
  out _ _ _ := Adjunction.hasLimitsOfShape_of_equivalence
    (PartialMaps.totalEquivalence (D := D)).inverse

local instance totalCoproducts : HasFiniteCoproducts (PartialMaps.Tot D) where
  out _ := Adjunction.hasColimitsOfShape_of_equivalence
    (PartialMaps.totalEquivalence (D := D)).inverse

omit [FinitaryExtensive D] in
theorem regular : Regular (PartialMaps.Tot D) :=
  RegularEquivalence.regular (PartialMaps.totalEquivalence (D := D))

local instance : Regular (PartialMaps.Tot D) := regular D

theorem extensive : FinitaryExtensive (PartialMaps.Tot D) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism
    (PartialMaps.totalEquivalence (D := D)).inverse

local instance : FinitaryExtensive (PartialMaps.Tot D) := extensive D

/-- The domains are subobjects in the total category of the actual monic
partial-map category. Its total equivalence covers all such subobjects. -/
theorem inseparable {S : D} (A B : Subobject S) (hi : SubobjectInseparable A B) :
    SubobjectInseparable
      (FiniteLimitSubobjects.object (PartialMaps.totalEquivalence (D := D)).functor A)
      (FiniteLimitSubobjects.object (PartialMaps.totalEquivalence (D := D)).functor B) :=
  EquivalenceSubobjects.inseparable (PartialMaps.totalEquivalence (D := D)) hi

end PartialTotals
end CategoricalEssentialIncompleteness.V46.SliceInseparability
