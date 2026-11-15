/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerAssociatedStructure

/-! # Corollary 9.8: the Miller associated recursion categories -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.AssociatedCategories
open AssociatedData AssociatedTheories AssociatedIncompleteness AssociatedStructure
variable (a : Point)
local instance (P : Total.CanonicalTotal a) : Regular (Over P) := RegularSlices.regular P
local instance (P : Total.CanonicalTotal a) : FinitaryExtensive (Over P) :=
  RegularSlices.finitaryExtensive P
local instance (P : Total.CanonicalTotal a) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P
local instance (P : Total.CanonicalTotal a) : Regular (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.regular (Over P)
local instance (P : Total.CanonicalTotal a) : FinitaryExtensive (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.extensive (Over P)

/-- All printed conclusions refer to the actual monic partial-map slice.
The stronger subobject quantifier includes every closed consistent extension. -/
structure Conclusions (U : Theory a) (hc : U.val ⊓ refutation a U = ⊥) : Prop where
  turing : Nonempty (CompatibleSplitSlices.TuringData
    (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))))
  constant_theory : (constantTheory a U).val =
    Subobject.mk ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map U.val.arrow)
  closed_consistent : (constantTheory a U).val ⊓ (Subobject.pullback
    ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
      (syntaxData a).sentenceNegation)).obj (constantTheory a U).val = ⊥
  closed_extensions : ∀ W : FirstOrderReflection.Theory
      (sliceProofs a (U.val : Total.CanonicalTotal a)), (constantTheory a U).val ≤ W.val →
    W.val ⊓ (Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
      (syntaxData a).sentenceNegation)).obj W.val = ⊥ →
    W.val ⊔ (Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
      (syntaxData a).sentenceNegation)).obj W.val ≠ ⊤
  actual_consistent : actualTheoryDomain a U ⊓ (Subobject.pullback (actualNegation a U)).obj
    (actualTheoryDomain a U) = ⊥
  actual_extensions : ∀ W : Subobject ((PartialMaps.totalEquivalence
      (D := Over (U.val : Total.CanonicalTotal a))).functor.obj
        (constantFamily (U.val : Total.CanonicalTotal a) (syntaxData a).sentenceObject)),
    actualTheoryDomain a U ≤ W → W ⊓ (Subobject.pullback (actualNegation a U)).obj W = ⊥ →
    W ⊔ (Subobject.pullback (actualNegation a U)).obj W ≠ ⊤
  actual_inseparable : SubobjectInseparable (actualTheoryDomain a U)
    ((Subobject.pullback (actualNegation a U)).obj (actualTheoryDomain a U))
  decision_domain : rst (decision a U hc) =
    (RestrictionSubobjects.domain (inverses a) (U.val ⊔ refutation a U)).hom
  decision_true : U.val.arrow.hom ≫ decision a U hc =
    (Two.constant (U.val : Total.CanonicalTotal a) true).hom
  decision_false : (refutation a U).arrow.hom ≫ decision a U hc =
    (Two.constant ((refutation a U) : Total.CanonicalTotal a) false).hom
  family_domain : rst ((constantFunctor a U).map (decision a U hc)) =
    (constantFunctor a U).map (RestrictionSubobjects.domain (inverses a)
      (U.val ⊔ refutation a U)).hom
  family_true : (constantFunctor a U).map U.val.arrow.hom ≫
    (constantFunctor a U).map (decision a U hc) =
      (constantFunctor a U).map (Two.constant (U.val : Total.CanonicalTotal a) true).hom
  family_false : (constantFunctor a U).map (refutation a U).arrow.hom ≫
    (constantFunctor a U).map (decision a U hc) = (constantFunctor a U).map
      (Two.constant ((refutation a U) : Total.CanonicalTotal a) false).hom
  no_total_extension : ¬ RestrictionRetraction.HasTotalExtension
    ((constantFunctor a U).map (decision a U hc))
  comparisons : ∀ (U' : Theory a)
      (i : (U.val : Total.CanonicalTotal a) ⟶ (U'.val : Total.CanonicalTotal a)) [Mono i],
    i ≫ U'.val.arrow = U.val.arrow → U'.val ⊓ refutation a U' = ⊥ →
    (postcompose a i).Full ∧ (postcompose a i).Faithful ∧
      PreservesRestriction (postcompose a i) ∧ (¬ IsIso i → ¬ (postcompose a i).EssSurj)

/-- Corollary 9.8 uses the printed Miller, closed-theory, extension and
consistency hypotheses; all deduction and comparison data are constructed. -/
theorem printed_statement (ha : IsMiller a) (U : Theory a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ refutation a U = ⊥) : Conclusions a U hc where
  turing := ⟨turingData a U⟩
  constant_theory := constantTheory_value a U
  closed_consistent := (essentially_incomplete a U ha hExt hc).1
  closed_extensions := (essentially_incomplete a U ha hExt hc).2
  actual_consistent := (actual_essentially_incomplete a U ha hExt hc).1
  actual_extensions := (actual_essentially_incomplete a U ha hExt hc).2
  actual_inseparable := actual_domains_inseparable a U ha hExt hc
  decision_domain := AssociatedStructure.decision_domain a U hc
  decision_true := AssociatedStructure.decision_true a U hc
  decision_false := AssociatedStructure.decision_false a U hc
  family_domain := AssociatedStructure.family_domain a U hc
  family_true := AssociatedStructure.family_true a U hc
  family_false := AssociatedStructure.family_false a U hc
  no_total_extension := AssociatedStructure.no_total_extension a U ha hExt hc
  comparisons := by
    intro U' i _hi _hfac _hc
    exact ⟨postcompose_full a i, postcompose_faithful a i,
      postcompose_restriction a i, postcompose_not_essSurj a i⟩

end CategoricalEssentialIncompleteness.V46.Miller.AssociatedCategories
