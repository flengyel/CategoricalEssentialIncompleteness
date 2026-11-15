/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticAssociatedIncompleteness
public import CategoricalEssentialIncompleteness.V46ConstantSliceFull
public import CategoricalEssentialIncompleteness.V46CompatibleSplitSlices
public import CategoricalEssentialIncompleteness.V46SplitSliceTuring

/-! # The actual arithmetic associated categories and their structural comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedStructure
open RestrictionSubobjects
abbrev Source := CodedProgramCategory 𝗣𝗔
abbrev Ambient := SplitObject Source
abbrev actualRestriction : RestrictionCategory Ambient := inferInstance

theorem inverses : MonoInverses Ambient := fun m => totalSplit_mono_partial_inverse 𝗣𝗔 m

local instance : PCategoryStruct Ambient := SplitObject.productData
local instance : PCategory Ambient := SplitObject.productLaws
local instance : RestrictionCategory Ambient := actualRestriction

theorem restriction_eq : PCategory.inducedRestriction =
    actualRestriction := SplitObject.productRestriction_eq

def constantData (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :=
  CompatiblePartialSlices.constantData (ρ := actualRestriction) restriction_eq
    inverses (ArithmeticAssociatedIncompleteness.point U)
      ArithmeticAssociatedDeduction.pointDomain_terminal

def constantFunctor (U : ArithmeticAssociatedIncompleteness.GlobalTheory) := (constantData U).val

theorem constant_faithful (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    (constantFunctor U).Faithful := (constantData U).property.1

def postcompose {T U : TotalSplit 𝗣𝗔} (i : T ⟶ U) :
    PartialMaps.Par (Over T) ⥤ PartialMaps.Par (Over U) :=
  CompatiblePartialSlices.postcompose (ρ := actualRestriction) restriction_eq i

theorem postcompose_full {T U : TotalSplit 𝗣𝗔} (i : T ⟶ U) [Mono i] :
    (postcompose i).Full :=
  CompatiblePartialSlices.postcompose_full (ρ := actualRestriction) restriction_eq inverses i

theorem postcompose_faithful {T U : TotalSplit 𝗣𝗔} (i : T ⟶ U) [Mono i] :
    (postcompose i).Faithful :=
  CompatiblePartialSlices.postcompose_faithful (ρ := actualRestriction) restriction_eq inverses i

theorem postcompose_not_essSurj {T U : TotalSplit 𝗣𝗔} (i : T ⟶ U) [Mono i]
    (proper : ¬ IsIso i) : ¬ (postcompose i).EssSurj :=
  CompatiblePartialSlices.postcompose_not_essSurj (ρ := actualRestriction)
    restriction_eq inverses i proper

local notation "F₀" => ArithmeticSignedTheory.presentation
local notation "ν" => ArithmeticSignedTotal.negation (F₀)

/-- The constructed Boolean partial morphism is true on the theorem
subobject and false on its actual negation inverse image. -/
def decision (U : ArithmeticAssociatedIncompleteness.GlobalTheory)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :=
  BooleanPartialDecision.decision inverses U.val ((Subobject.pullback (ν)).obj U.val) hc

theorem decision_true (U : ArithmeticAssociatedIncompleteness.GlobalTheory)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    U.val.arrow.hom ≫ decision U hc = (Two.constant (U.val : TotalSplit 𝗣𝗔) true).hom :=
  BooleanPartialDecision.positive_value inverses _ _ hc

theorem decision_false (U : ArithmeticAssociatedIncompleteness.GlobalTheory)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    ((Subobject.pullback (ν)).obj U.val).arrow.hom ≫ decision U hc =
      (Two.constant (((Subobject.pullback (ν)).obj U.val) : TotalSplit 𝗣𝗔) false).hom :=
  BooleanPartialDecision.negative_value inverses _ _ hc

/-- Both directions of the existing restriction retraction are reused.
The resulting morphism lies in the actual associated partial-map slice. -/
theorem no_total_extension (U : ArithmeticAssociatedIncompleteness.GlobalTheory)
    (hExt : (ArithmeticSignedTotal.theory (F₀)).val ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    ¬ RestrictionRetraction.HasTotalExtension ((constantFunctor U).map (decision U hc)) := by
  have hi := ArithmeticAssociatedIncompleteness.extension_inseparable U hExt hc
  have hn : ¬ RestrictionRetraction.HasTotalExtension (decision U hc) :=
    (BooleanPartialDecision.inseparable_iff_noTotalExtension inverses _ _ hc).mp hi
  intro he
  exact hn (((constantData U).property.2.2 _).mp he)

/-- Every actual parameter slice has a split universal Turing object. -/
def turingData (T : TotalSplit 𝗣𝗔) :=
  CompatibleSplitSlices.turingData (ρ := actualRestriction) restriction_eq inverses T
    (inferInstance : RecursionCategory.PRecursionCategory Source)

/-- The literal full subcategory consists of U × X for original source objects. -/
abbrev FullCategory (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :=
  ConstantSlice.Full.FullCategory (U.val : TotalSplit 𝗣𝗔).obj

/-- Its recursion-category structure is constructed from the existing
arithmetic recursion category. -/
@[instance_reducible] def recursionCategory (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :=
  CompatibleSplitSlices.recursionCategory (ρ := actualRestriction) restriction_eq inverses
    (U.val : TotalSplit 𝗣𝗔) (inferInstance : RecursionCategory.PRecursionCategory Source)

def fullInclusion (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    FullCategory U ⥤ PartialMaps.Par (Over (U.val : TotalSplit 𝗣𝗔)) :=
  CompatibleSplitSlices.inclusion (ρ := actualRestriction) restriction_eq inverses
    (U.val : TotalSplit 𝗣𝗔)

theorem fullInclusion_full (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    (fullInclusion U).Full :=
  CompatibleSplitSlices.inclusion_full (ρ := actualRestriction) restriction_eq inverses _

theorem fullInclusion_faithful (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    (fullInclusion U).Faithful :=
  CompatibleSplitSlices.inclusion_faithful (ρ := actualRestriction) restriction_eq inverses _

def splittingEquivalence (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    SplitObject (FullCategory U) ≌ PartialMaps.Par (Over (U.val : TotalSplit 𝗣𝗔)) :=
  CompatibleSplitSlices.splittingEquivalence (ρ := actualRestriction) restriction_eq inverses
    (U.val : TotalSplit 𝗣𝗔) (RecursionCategory.PRecursionCategory.W (C := Source))

theorem decision_family_true (U : ArithmeticAssociatedIncompleteness.GlobalTheory)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    (constantFunctor U).map U.val.arrow.hom ≫ (constantFunctor U).map (decision U hc) =
      (constantFunctor U).map (Two.constant (U.val : TotalSplit 𝗣𝗔) true).hom := by
  rw [← CategoryTheory.Functor.map_comp, decision_true]

theorem decision_family_false (U : ArithmeticAssociatedIncompleteness.GlobalTheory)
    (hc : U.val ⊓ (Subobject.pullback (ν)).obj U.val = ⊥) :
    (constantFunctor U).map (((Subobject.pullback (ν)).obj U.val).arrow.hom) ≫
        (constantFunctor U).map (decision U hc) =
      (constantFunctor U).map
        (Two.constant (((Subobject.pullback (ν)).obj U.val) : TotalSplit 𝗣𝗔) false).hom := by
  rw [← CategoryTheory.Functor.map_comp, decision_false]


theorem fullInclusion_restriction (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    PreservesRestriction (fullInclusion U) :=
  CompatibleSplitSlices.inclusion_restriction (ρ := actualRestriction) restriction_eq inverses _

theorem splitting_restriction (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    PreservesRestriction (splittingEquivalence U).functor :=
  CompatibleSplitSlices.splitting_restriction (ρ := actualRestriction) restriction_eq inverses _ _

theorem splitting_inverse_restriction (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    PreservesRestriction (splittingEquivalence U).inverse :=
  CompatibleSplitSlices.splitting_inverse_restriction (ρ := actualRestriction)
    restriction_eq inverses _ _

local instance originalPullbacks :
    HasPullbacks (@Tot Ambient inferInstance PCategory.inducedRestriction) :=
  CompatibleSplitSlices.pullbacks (ρ := actualRestriction) restriction_eq

local instance originalRestriction : RestrictionCategory Ambient :=
  PCategory.inducedRestriction

theorem fullProducts_restriction_eq (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    @PCategory.inducedRestriction (FullCategory U) inferInstance
      (ConstantSlice.Full.productData (U.val : TotalSplit 𝗣𝗔).obj)
      (ConstantSlice.Full.productLaws (U.val : TotalSplit 𝗣𝗔).obj) =
        (inferInstance : RestrictionCategory (FullCategory U)) :=
  ConstantSlice.Full.productRestriction_eq _

def originalFunctor (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    Source ⥤ FullCategory U := OriginalConstantFunctor.functor (U.val : TotalSplit 𝗣𝗔).obj

theorem original_faithful (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    (originalFunctor U).Faithful :=
  CompatibleSplitSlices.original_faithful (ρ := actualRestriction) restriction_eq inverses
    (U.val : TotalSplit 𝗣𝗔) (ArithmeticAssociatedIncompleteness.point U)
    ArithmeticAssociatedDeduction.pointDomain_terminal

/-- This is exactly the printed morphism f ↦ 1_U × f on underlying programs. -/
theorem original_value (U : ArithmeticAssociatedIncompleteness.GlobalTheory)
    {X Y : Source} (f : X ⟶ Y) :
    (((originalFunctor U).map f).hom.hom).hom =
      PCategoryStruct.nearProd_map (U.val : TotalSplit 𝗣𝗔).obj.domain.hom f := rfl

def originalProductComparison (U : ArithmeticAssociatedIncompleteness.GlobalTheory) (X Y : Source) :=
  OriginalConstantFunctor.productComparison (U.val : TotalSplit 𝗣𝗔).obj X Y

/-- No new universal program is selected: this is the image of τ_PA under
its canonical product comparison. -/
def originalEvaluator (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :=
  OriginalConstantFunctor.evaluator (U.val : TotalSplit 𝗣𝗔).obj
    (FailureOfComposition.TypedTuringMorphism.typedTau 𝗣𝗔)

theorem original_evaluator_isTuring (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    @RecursionCategory.IsTuringMorphism (FullCategory U) inferInstance
      (ConstantSlice.Full.productData (U.val : TotalSplit 𝗣𝗔).obj)
      (ConstantSlice.Full.productLaws (U.val : TotalSplit 𝗣𝗔).obj)
      ((originalFunctor U).obj (omegaObject 𝗣𝗔)) ((originalFunctor U).obj (omegaObject 𝗣𝗔))
      ((originalFunctor U).obj (omegaObject 𝗣𝗔)) (originalEvaluator U) :=
  OriginalConstantFunctor.evaluator_isTuring _ _
    (FailureOfComposition.TypedTuringMorphism.typedTau_isTuringMorphism 𝗣𝗔)

theorem original_evaluator_value (U : ArithmeticAssociatedIncompleteness.GlobalTheory) :
    originalEvaluator U =
      (originalProductComparison U (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom ≫
        (originalFunctor U).map (FailureOfComposition.TypedTuringMorphism.typedTau 𝗣𝗔) := rfl

end CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedStructure
