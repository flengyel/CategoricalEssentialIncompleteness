/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticAssociatedCategories

/-! # Independent checks of every printed clause of Corollary 8.10 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 SyntacticPredicates RestrictionSubobjects RecursionCategory
open ArithmeticAssociatedIncompleteness ArithmeticAssociatedStructure
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

example (hPA : Entailment.Consistent 𝗣𝗔) (U : GlobalTheory)
    (hExt : (t).val ≤ U.val) (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    ArithmeticAssociatedCategories.Conclusions U hExt hc :=
  ArithmeticAssociatedCategories.printed_statement hPA U hExt hc

example (U : GlobalTheory) (hExt : (t).val ≤ U.val) :
    Subobject.ofLE (t).val U.val hExt ≫ U.val.arrow = (t).val.arrow ∧
    (postcompose (Subobject.ofLE (t).val U.val hExt)).Full ∧
    (postcompose (Subobject.ofLE (t).val U.val hExt)).Faithful ∧
    (¬ IsIso (Subobject.ofLE (t).val U.val hExt) →
      ¬ (postcompose (Subobject.ofLE (t).val U.val hExt)).EssSurj) :=
  ⟨Subobject.ofLE_arrow hExt, postcompose_full _, postcompose_faithful _,
    postcompose_not_essSurj _⟩

/-- Both T_pm and every U have genuine universal objects in their actual
partial-map slices, including all nonconstant slice objects. -/
example (T : TotalSplit 𝗣𝗔) :
    ∃ (products : PCategoryStruct (PartialMaps.Par (Over T)))
      (laws : @PCategory (PartialMaps.Par (Over T)) inferInstance products),
    @PCategory.inducedRestriction (PartialMaps.Par (Over T)) inferInstance products laws =
      (inferInstance : RestrictionCategory (PartialMaps.Par (Over T))) ∧
    ∃ (Q : PartialMaps.Par (Over T))
      (τ : @PCategoryStruct.nearProd (PartialMaps.Par (Over T)) inferInstance products Q Q ⟶ Q),
    @IsTuringMorphism (PartialMaps.Par (Over T)) inferInstance products laws Q Q Q τ ∧
    (∀ X : PartialMaps.Par (Over T), ∃ (j : X ⟶ Q) (s : Q ⟶ X),
      isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = CategoryTheory.RestrictionCategory.rst s) ∧
    Nonempty (Splits (PartialMaps.Par (Over T))) := by
  let d := turingData T
  exact ⟨d.products, d.laws, d.restriction_eq, d.Q, d.evaluator, d.turing,
    d.universal, ⟨d.splittings⟩⟩

example (U : GlobalTheory) (hExt : (t).val ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    (constantTheory U).val =
      Subobject.mk ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map U.val.arrow) ∧
    ((constantTheory U).val ⊓ (Subobject.pullback
      ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map (ν))).obj (constantTheory U).val = ⊥) ∧
    ∀ W : FirstOrderReflection.Theory (ArithmeticAssociatedDeduction.proofs
        (U.val : TotalSplit 𝗣𝗔)), (constantTheory U).val ≤ W.val →
      W.val ⊓ (Subobject.pullback ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map (ν))).obj
        W.val = ⊥ →
      W.val ⊔ (Subobject.pullback ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map (ν))).obj
        W.val ≠ ⊤ :=
  ⟨constantTheory_value U, essentially_incomplete U hExt hc⟩

example (U : GlobalTheory) (hExt : (t).val ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    ((constantFunctor U).map U.val.arrow.hom ≫ (constantFunctor U).map (decision U hc) =
      (constantFunctor U).map (CategoricalEssentialIncompleteness.Two.constant (U.val : TotalSplit 𝗣𝗔) true).hom) ∧
    ((constantFunctor U).map (((Subobject.pullback (ν)).obj U.val).arrow.hom) ≫
      (constantFunctor U).map (decision U hc) = (constantFunctor U).map
        (CategoricalEssentialIncompleteness.Two.constant (((Subobject.pullback (ν)).obj U.val) : TotalSplit 𝗣𝗔) false).hom) ∧
    ¬ RestrictionRetraction.HasTotalExtension ((constantFunctor U).map (decision U hc)) :=
  ⟨decision_family_true U hc, decision_family_false U hc, no_total_extension U hExt hc⟩

example (U : GlobalTheory) : (fullInclusion U).Full ∧ (fullInclusion U).Faithful ∧
    ∀ Z : PartialMaps.Par (Over (U.val : TotalSplit 𝗣𝗔)),
      (∃ X : FullCategory U, (fullInclusion U).obj X = Z) ↔
        ∃ X : Source, (fullInclusion U).obj
          (ConstantSlice.Full.object (U.val : TotalSplit 𝗣𝗔).obj X) = Z :=
  ⟨fullInclusion_full U, fullInclusion_faithful U,
    CompatibleSplitSlices.inclusion_range (ρ := actualRestriction) restriction_eq inverses _⟩

example (U : GlobalTheory) :
    @PRecursionCategory (FullCategory U) inferInstance
      (ConstantSlice.Full.productData (U.val : TotalSplit 𝗣𝗔).obj)
      (ConstantSlice.Full.productLaws (U.val : TotalSplit 𝗣𝗔).obj)
      inferInstance (ConstantSlice.Full.prodominical (U.val : TotalSplit 𝗣𝗔).obj)
      (ConstantSlice.Full.isotype (U.val : TotalSplit 𝗣𝗔).obj) := recursionCategory U

example (U : GlobalTheory) :
    SplitObject (FullCategory U) ≌ PartialMaps.Par (Over (U.val : TotalSplit 𝗣𝗔)) :=
  splittingEquivalence U

example (U : GlobalTheory) : (originalFunctor U).Faithful := original_faithful U

example (U : GlobalTheory) : originalEvaluator U =
    (originalProductComparison U (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom ≫
      (originalFunctor U).map (FailureOfComposition.TypedTuringMorphism.typedTau 𝗣𝗔) :=
  original_evaluator_value U

example (U : GlobalTheory) :
    @IsTuringMorphism (FullCategory U) inferInstance
      (ConstantSlice.Full.productData (U.val : TotalSplit 𝗣𝗔).obj)
      (ConstantSlice.Full.productLaws (U.val : TotalSplit 𝗣𝗔).obj)
      ((originalFunctor U).obj (omegaObject 𝗣𝗔)) ((originalFunctor U).obj (omegaObject 𝗣𝗔))
      ((originalFunctor U).obj (omegaObject 𝗣𝗔)) (originalEvaluator U) := original_evaluator_isTuring U

section OriginalPrograms
local instance : RestrictionCategory Ambient := PCategory.inducedRestriction
/-- The identity of a split object has underlying program its domain
idempotent; this checks the literal printed 1_U × f at program level. -/
example (U : GlobalTheory) {X Y : Source} (f : X ⟶ Y) :
    (((originalFunctor U).map f).hom.hom).hom =
      PCategoryStruct.nearProd_map (U.val : TotalSplit 𝗣𝗔).obj.domain.hom f := original_value U f
end OriginalPrograms

#print axioms CompatiblePartialSlices.constantData
#print axioms CompatiblePartialSlices.postcompose_full
#print axioms CompatiblePartialSlices.postcompose_not_essSurj
#print axioms CompatibleSplitSlices.turingData
#print axioms CompatibleSplitSlices.recursionCategory
#print axioms CompatibleSplitSlices.splittingEquivalence
#print axioms CompatibleSplitSlices.original_faithful
#print axioms CompatibleSplitSlices.inclusion_range
#print axioms OriginalConstantFunctor.functor
#print axioms OriginalConstantFunctor.faithful
#print axioms OriginalConstantFunctor.productComparison
#print axioms OriginalConstantFunctor.ambient_evaluator
#print axioms OriginalConstantFunctor.evaluator_isTuring
#print axioms ArithmeticAssociatedStructure.decision
#print axioms ArithmeticAssociatedStructure.no_total_extension
#print axioms ArithmeticAssociatedStructure.turingData
#print axioms ArithmeticAssociatedStructure.recursionCategory
#print axioms ArithmeticAssociatedStructure.splittingEquivalence
#print axioms ArithmeticAssociatedStructure.original_faithful
#print axioms ArithmeticAssociatedStructure.original_value
#print axioms ArithmeticAssociatedStructure.original_evaluator_isTuring
#print axioms ArithmeticAssociatedCategories.printed_statement
