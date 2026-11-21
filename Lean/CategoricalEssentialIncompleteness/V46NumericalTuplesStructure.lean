/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalTuples
public import CategoricalEssentialIncompleteness.EnumerableExtensive
public import CategoricalEssentialIncompleteness.RestrictionSpans
public import CategoricalEssentialIncompleteness.V46SplitSplittings
public import CategoricalEssentialIncompleteness.EnumerableLocalConnectedness
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular

/-! # Regularity, extensive sums and partial inverses for tuple maps -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.NumericalTuples

instance tupleHasFiniteLimits : HasFiniteLimits Object where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence comparison

instance tupleStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations Object :=
  equivalence.inverse.hasStrongEpiMonoFactorisations_imp_of_isEquivalence

/-- The numerical image factorization has a split quotient; extremality
makes its inclusion invertible for every strong epimorphism. -/
theorem numericalStrongEpi_split {X Y : EnumerableCarriers.Total} (f : X ⟶ Y) [StrongEpi f] :
    IsSplitEpi f := by
  let : IsIso (EnumerableCarriers.imageInclusion f) :=
    ExtremalEpi.isIso f (EnumerableCarriers.imageQuotient f)
      (EnumerableCarriers.imageInclusion f) (EnumerableCarriers.image_factorization f)
  rw [← EnumerableCarriers.image_factorization f]
  infer_instance

theorem tupleStrongEpi_split {C D : Object} (f : C ⟶ D) [StrongEpi f] : IsSplitEpi f := by
  let : IsSplitEpi (comparison.map f) := numericalStrongEpi_split (comparison.map f)
  refine IsSplitEpi.mk' ⟨comparison.preimage (section_ (comparison.map f)), ?_⟩
  apply comparison.map_injective
  simp

instance tupleRegular : Regular Object :=
  SyntacticPredicates.regularOfSplitStrongEpis tupleStrongEpi_split

instance tupleHasFiniteCoproducts : HasFiniteCoproducts Object where
  out _ := Adjunction.hasColimitsOfShape_of_equivalence comparison

/-- Extensivity supplies disjointness and pullback stability of every finite coproduct in
the tuple-function category. -/
instance tupleFinitaryExtensive : FinitaryExtensive Object :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism comparison

/-- The ordinary total comparison followed by the restriction splitting inclusion. -/
def splitComparison : Object ⥤ SplitObject ClassicalPrograms.Rec :=
  classicalTotalEquivalence.functor ⋙
    PreservesRestriction.totalInclusion (SplitObject ClassicalPrograms.Rec)

/-- The partial inverse is a morphism of the classical splitting, constructed by the
already proved choice/monomorphism inverse theorem. -/
def monoInverse {C D : Object} (m : C ⟶ D) [Mono m] :
    splitComparison.obj D ⟶ splitComparison.obj C :=
  EnumerableCarriers.inclusion.map (PartialSpans.inverse (comparison.map m))

@[simp] theorem mappedMono_inverse {C D : Object} (m : C ⟶ D) [Mono m] :
    splitComparison.map m ≫ monoInverse m = 𝟙 (splitComparison.obj C) := by
  change EnumerableCarriers.inclusion.map (comparison.map m).hom ≫
    EnumerableCarriers.inclusion.map (PartialSpans.inverse (comparison.map m)) = 𝟙 _
  rw [← EnumerableCarriers.inclusion.map_comp, PartialSpans.hom_inverse,
    EnumerableCarriers.inclusion.map_id]

@[simp] theorem inverse_mappedMono {C D : Object} (m : C ⟶ D) [Mono m] :
    monoInverse m ≫ splitComparison.map m = rst (monoInverse m) := by
  change EnumerableCarriers.inclusion.map (PartialSpans.inverse (comparison.map m)) ≫
    EnumerableCarriers.inclusion.map (comparison.map m).hom = rst _
  rw [← EnumerableCarriers.inclusion.map_comp, PartialSpans.inverse_hom,
    EnumerableCarriers.inclusion_rst]
  rfl

/-- The partial inverse makes each mapped tuple mono a restriction monomorphism, with no
choice assumption on the target. -/
theorem mappedMono_partialMono {C D : Object} (m : C ⟶ D) [Mono m] :
    PartialMono (splitComparison.map m) := by
  intro W g h he
  have hh : g = h := by
    have hk := congrArg (fun f => f ≫ monoInverse m) he
    simpa only [Category.assoc, mappedMono_inverse, Category.comp_id] using hk
  rw [hh]

end CategoricalEssentialIncompleteness.V46.NumericalTuples
