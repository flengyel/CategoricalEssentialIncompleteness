/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerAssociatedIncompleteness
public import CategoricalEssentialIncompleteness.V46NativeSplitSlices

/-! # Miller associated Turing categories and their Boolean morphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.AssociatedStructure
open RestrictionSubobjects AssociatedData AssociatedTheories
variable (a : Point)

/-- The comparison is proved for the original uniform category; no fixed oracle
representation replaces its restriction structure. -/
theorem source_restriction_eq :
    (PCategory.inducedRestriction : RestrictionCategory (Uniform.PointObject a)) =
      Uniform.nativeRestriction :=
  NativeSplitSlices.restriction_ext _ _ (fun f => Uniform.induced_restriction f)

variable (U : Theory a)

def constantData := NativeSplitSlices.constantData (ρ := Uniform.nativeRestriction)
  (source_restriction_eq a) (inverses a) (point a U) (pointDomain_terminal a)

def constantFunctor := (constantData a U).val

def turingData := NativeSplitSlices.turingData (ρ := Uniform.nativeRestriction)
  (source_restriction_eq a) (inverses a) (U.val : Total.CanonicalTotal a)
    (Uniform.recursionCategory a)

def decision (hc : U.val ⊓ refutation a U = ⊥) :=
  BooleanPartialDecision.decision (inverses a) U.val (refutation a U) hc

theorem decision_domain (hc : U.val ⊓ refutation a U = ⊥) :
    rst (decision a U hc) = (domain (inverses a) (U.val ⊔ refutation a U)).hom :=
  BooleanPartialDecision.domain_eq (inverses a) _ _ hc

theorem decision_true (hc : U.val ⊓ refutation a U = ⊥) :
    U.val.arrow.hom ≫ decision a U hc =
      (Two.constant (U.val : Total.CanonicalTotal a) true).hom :=
  BooleanPartialDecision.positive_value (inverses a) _ _ hc

theorem decision_false (hc : U.val ⊓ refutation a U = ⊥) :
    (refutation a U).arrow.hom ≫ decision a U hc =
      (Two.constant ((refutation a U) : Total.CanonicalTotal a) false).hom :=
  BooleanPartialDecision.negative_value (inverses a) _ _ hc

theorem family_domain (hc : U.val ⊓ refutation a U = ⊥) :
    rst ((constantFunctor a U).map (decision a U hc)) =
      (constantFunctor a U).map (domain (inverses a) (U.val ⊔ refutation a U)).hom := by
  erw [← (constantData a U).property.2.1, decision_domain]
  rfl

theorem family_true (hc : U.val ⊓ refutation a U = ⊥) :
    (constantFunctor a U).map U.val.arrow.hom ≫
        (constantFunctor a U).map (decision a U hc) =
      (constantFunctor a U).map (Two.constant (U.val : Total.CanonicalTotal a) true).hom := by
  rw [← CategoryTheory.Functor.map_comp, decision_true]

theorem family_false (hc : U.val ⊓ refutation a U = ⊥) :
    (constantFunctor a U).map (refutation a U).arrow.hom ≫
        (constantFunctor a U).map (decision a U hc) =
      (constantFunctor a U).map
        (Two.constant ((refutation a U) : Total.CanonicalTotal a) false).hom := by
  rw [← CategoryTheory.Functor.map_comp, decision_false]

/-- The existing inseparability criterion and both total-extension retraction directions
are reused for the constant-family morphism. -/
theorem no_total_extension (ha : IsMiller a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ refutation a U = ⊥) :
    ¬ RestrictionRetraction.HasTotalExtension ((constantFunctor a U).map (decision a U hc)) := by
  have hi := (global_incompleteness a ha U hExt hc).1
  have hn : ¬ RestrictionRetraction.HasTotalExtension (decision a U hc) :=
    (BooleanPartialDecision.inseparable_iff_noTotalExtension (inverses a) _ _ hc).mp hi
  intro he
  exact hn (((constantData a U).property.2.2 _).mp he)

def comparisonData {T W : Total.CanonicalTotal a} (i : T ⟶ W) [Mono i] :=
  NativeSplitSlices.postcomposeData (ρ := Uniform.nativeRestriction)
    (source_restriction_eq a) (inverses a) i

def postcompose {T W : Total.CanonicalTotal a} (i : T ⟶ W) [Mono i] := (comparisonData a i).val

theorem postcompose_full {T W : Total.CanonicalTotal a} (i : T ⟶ W) [Mono i] :
    (postcompose a i).Full := (comparisonData a i).property.1

theorem postcompose_faithful {T W : Total.CanonicalTotal a} (i : T ⟶ W) [Mono i] :
    (postcompose a i).Faithful := (comparisonData a i).property.2.1

theorem postcompose_restriction {T W : Total.CanonicalTotal a} (i : T ⟶ W) [Mono i] :
    PreservesRestriction (postcompose a i) := (comparisonData a i).property.2.2.1

theorem postcompose_not_essSurj {T W : Total.CanonicalTotal a} (i : T ⟶ W) [Mono i]
    (proper : ¬ IsIso i) : ¬ (postcompose a i).EssSurj := (comparisonData a i).property.2.2.2 proper

end CategoricalEssentialIncompleteness.V46.Miller.AssociatedStructure
