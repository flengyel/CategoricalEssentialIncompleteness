/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticAssociatedStructure

/-! # Corollary 8.10: the arithmetic associated categories -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedCategories
open RestrictionSubobjects RecursionCategory ArithmeticAssociatedIncompleteness
open ArithmeticAssociatedStructure
local notation "F₀" => ArithmeticSignedTheory.presentation
local notation "ν" => ArithmeticSignedTotal.negation (F₀)
local notation "t" => ArithmeticSignedTotal.theory (F₀)
local instance : PCategoryStruct Ambient := SplitObject.productData
local instance : PCategory Ambient := SplitObject.productLaws
local instance : RestrictionCategory Ambient := actualRestriction
local instance : HasPullbacks (@Tot Ambient inferInstance PCategory.inducedRestriction) :=
  CompatibleSplitSlices.pullbacks (ρ := actualRestriction) restriction_eq
local instance (P : TotalSplit 𝗣𝗔) : Regular (Over P) := RegularSlices.regular P
local instance (P : TotalSplit 𝗣𝗔) : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance (P : TotalSplit 𝗣𝗔) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

/-- Every conclusion, with the original arithmetic theory and unrestricted closed
slice-extension quantifier retained. -/
structure Conclusions (U : GlobalTheory) (hExt : (t).val ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) : Prop where
  factorization : Subobject.ofLE (t).val U.val hExt ≫ U.val.arrow = (t).val.arrow
  full : (postcompose (Subobject.ofLE (t).val U.val hExt)).Full
  faithful : (postcompose (Subobject.ofLE (t).val U.val hExt)).Faithful
  proper : ¬ IsIso (Subobject.ofLE (t).val U.val hExt) →
    ¬ (postcompose (Subobject.ofLE (t).val U.val hExt)).EssSurj
  base_split_turing : Nonempty (CompatibleSplitSlices.TuringData
    (PartialMaps.Par (Over ((t).val : TotalSplit 𝗣𝗔))))
  extension_split_turing : Nonempty (CompatibleSplitSlices.TuringData
    (PartialMaps.Par (Over (U.val : TotalSplit 𝗣𝗔))))
  constant_theory : (constantTheory U).val =
    Subobject.mk ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map U.val.arrow)
  consistent : (constantTheory U).val ⊓ (Subobject.pullback
    ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map (ν))).obj (constantTheory U).val = ⊥
  extensions : ∀ W : FirstOrderReflection.Theory (ArithmeticAssociatedDeduction.proofs
      (U.val : TotalSplit 𝗣𝗔)), (constantTheory U).val ≤ W.val →
    W.val ⊓ (Subobject.pullback ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map (ν))).obj
      W.val = ⊥ →
    W.val ⊔ (Subobject.pullback ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map (ν))).obj
      W.val ≠ ⊤
  boolean_true : (constantFunctor U).map U.val.arrow.hom ≫
      (constantFunctor U).map (decision U hc) =
    (constantFunctor U).map (Two.constant (U.val : TotalSplit 𝗣𝗔) true).hom
  boolean_false : (constantFunctor U).map (((Subobject.pullback (ν)).obj U.val).arrow.hom) ≫
      (constantFunctor U).map (decision U hc) = (constantFunctor U).map
        (Two.constant (((Subobject.pullback (ν)).obj U.val) : TotalSplit 𝗣𝗔) false).hom
  no_total_extension : ¬ RestrictionRetraction.HasTotalExtension
    ((constantFunctor U).map (decision U hc))
  full_subcategory : (fullInclusion U).Full
  faithful_subcategory : (fullInclusion U).Faithful
  restriction_subcategory : PreservesRestriction (fullInclusion U)
  products_restriction : @PCategory.inducedRestriction (FullCategory U) inferInstance
    (ConstantSlice.Full.productData (U.val : TotalSplit 𝗣𝗔).obj)
    (ConstantSlice.Full.productLaws (U.val : TotalSplit 𝗣𝗔).obj) =
      (inferInstance : RestrictionCategory (FullCategory U))
  original_objects : ∀ Z : PartialMaps.Par (Over (U.val : TotalSplit 𝗣𝗔)),
    (∃ X : FullCategory U, (fullInclusion U).obj X = Z) ↔
      ∃ X : Source, (fullInclusion U).obj
        (ConstantSlice.Full.object (U.val : TotalSplit 𝗣𝗔).obj X) = Z
  recursion : Nonempty (@PRecursionCategory (FullCategory U) inferInstance
    (ConstantSlice.Full.productData (U.val : TotalSplit 𝗣𝗔).obj)
    (ConstantSlice.Full.productLaws (U.val : TotalSplit 𝗣𝗔).obj)
    inferInstance (ConstantSlice.Full.prodominical (U.val : TotalSplit 𝗣𝗔).obj)
    (ConstantSlice.Full.isotype (U.val : TotalSplit 𝗣𝗔).obj))
  splitting : Nonempty (SplitObject (FullCategory U) ≌
    PartialMaps.Par (Over (U.val : TotalSplit 𝗣𝗔)))
  splitting_restriction : PreservesRestriction (splittingEquivalence U).functor
  splitting_inverse_restriction : PreservesRestriction (splittingEquivalence U).inverse
  original_faithful : (originalFunctor U).Faithful
  original_evaluator : originalEvaluator U =
    (originalProductComparison U (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom ≫
      (originalFunctor U).map (FailureOfComposition.TypedTuringMorphism.typedTau 𝗣𝗔)
  original_turing : @IsTuringMorphism (FullCategory U) inferInstance
    (ConstantSlice.Full.productData (U.val : TotalSplit 𝗣𝗔).obj)
    (ConstantSlice.Full.productLaws (U.val : TotalSplit 𝗣𝗔).obj)
    ((originalFunctor U).obj (omegaObject 𝗣𝗔)) ((originalFunctor U).obj (omegaObject 𝗣𝗔))
    ((originalFunctor U).obj (omegaObject 𝗣𝗔)) (originalEvaluator U)

/-- Corollary 8.10 uses only the assumptions. Deduction initiality, closure transfer,
inseparability and all categorical structures are constructed. -/
theorem printed_statement (_hPA : Entailment.Consistent 𝗣𝗔) (U : GlobalTheory)
    (hExt : (t).val ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) : Conclusions U hExt hc where
  factorization := Subobject.ofLE_arrow hExt
  full := postcompose_full _
  faithful := postcompose_faithful _
  proper := postcompose_not_essSurj _
  base_split_turing := ⟨turingData _⟩
  extension_split_turing := ⟨turingData _⟩
  constant_theory := constantTheory_value U
  consistent := (essentially_incomplete U hExt hc).1
  extensions := (essentially_incomplete U hExt hc).2
  boolean_true := decision_family_true U hc
  boolean_false := decision_family_false U hc
  no_total_extension := no_total_extension U hExt hc
  full_subcategory := fullInclusion_full U
  faithful_subcategory := fullInclusion_faithful U
  restriction_subcategory := fullInclusion_restriction U
  products_restriction := fullProducts_restriction_eq U
  original_objects := CompatibleSplitSlices.inclusion_range (ρ := actualRestriction)
    restriction_eq inverses (U.val : TotalSplit 𝗣𝗔)
  recursion := ⟨recursionCategory U⟩
  splitting := ⟨splittingEquivalence U⟩
  splitting_restriction := ArithmeticAssociatedStructure.splitting_restriction U
  splitting_inverse_restriction := ArithmeticAssociatedStructure.splitting_inverse_restriction U
  original_faithful := ArithmeticAssociatedStructure.original_faithful U
  original_evaluator := original_evaluator_value U
  original_turing := original_evaluator_isTuring U

end CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedCategories
