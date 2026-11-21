/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AssociatedExtensionWitness

/-! # The restriction retraction and the partial Boolean morphism -/

@[expose] public section
noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionSubobjects AssociatedCategory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)] (inverses : MonoInverses C)
variable {Z U : Tot C} (point : Z ⟶ U) (hZ : IsTerminal Z)

example : PartialSliceTheoryFamilies.constantFunctor inverses U ⋙
    evaluation inverses point ≅ 𝟭 C := retraction inverses point hZ

example : PreservesRestriction (evaluation inverses point) := evaluation_restriction inverses point

example : PreservesRestriction (PartialSliceTheoryFamilies.constantFunctor inverses U) :=
  constant_restriction inverses U

example : (PartialSliceTheoryFamilies.constantFunctor inverses U).Faithful :=
  constant_faithful inverses point hZ

example (Y : PartialMaps.Par (Over U)) :
    (evaluation inverses point).obj Y = (pullback Y.obj.hom point).obj :=
  evaluation_object inverses point Y

example : evaluation inverses point =
    PartialSliceChangeBase.spanPullback point ⋙ PartialSliceEquivalence.baseFunctor inverses Z :=
  evaluation_spanPullback inverses point

example {X Y : C} (f : X ⟶ Y) :
    isTotal ((PartialSliceTheoryFamilies.constantFunctor inverses U).map f) ↔ isTotal f :=
  constant_total_iff inverses point hZ f

example {X Y : C} (f : X ⟶ Y) :
    (∃ g : (PartialSliceTheoryFamilies.constantFunctor inverses U).obj X ⟶
        (PartialSliceTheoryFamilies.constantFunctor inverses U).obj Y,
      isTotal g ∧ rst ((PartialSliceTheoryFamilies.constantFunctor inverses U).map f) ≫ g =
        (PartialSliceTheoryFamilies.constantFunctor inverses U).map f) ↔
      ∃ g : X ⟶ Y, isTotal g ∧ rst f ≫ g = f :=
  hasTotalExtension_iff inverses point hZ f

variable {X : Tot C} (a b : Subobject X) (hab : a ⊓ b = ⊥)

example : rst (BooleanPartialDecision.decision inverses a b hab) =
    (domain inverses (a ⊔ b)).hom := BooleanPartialDecision.domain_eq inverses a b hab

example : a.arrow.hom ≫ BooleanPartialDecision.decision inverses a b hab =
    (CategoricalEssentialIncompleteness.Two.constant (a : Tot C) true).hom :=
  BooleanPartialDecision.positive_value inverses a b hab

example : b.arrow.hom ≫ BooleanPartialDecision.decision inverses a b hab =
    (CategoricalEssentialIncompleteness.Two.constant (b : Tot C) false).hom :=
  BooleanPartialDecision.negative_value inverses a b hab

example : isTotal (BooleanPartialDecision.decision inverses a b hab) ↔ a ⊔ b = ⊤ :=
  BooleanPartialDecision.total_iff inverses a b hab

example : RestrictionRetraction.HasTotalExtension
    (BooleanPartialDecision.decision inverses a b hab) ↔ HasSubobjectSeparator a b :=
  BooleanPartialDecision.hasTotalExtension_iff_separator inverses a b hab

variable {V : Tot C} (P : FirstOrderPresentation V)
variable (T : Subobject P.syntaxData.sentenceObject) (hc : P.Consistent T)

example : rst (theoryDecision inverses P T hc) =
    (domain inverses (T ⊔ (Subobject.pullback P.syntaxData.sentenceNegation).obj T)).hom :=
  theoryDecision_domain inverses P T hc

example (pointT : Z ⟶ (T : Tot C)) :
    ¬ P.Complete T ↔
      ¬ isTotal ((PartialSliceTheoryFamilies.constantFunctor inverses (T : Tot C)).map
        (theoryDecision inverses P T hc)) :=
  incomplete_iff_decision_not_total inverses P T hc pointT hZ

example (pointT : Z ⟶ (T : Tot C)) :
    SubobjectInseparable T ((Subobject.pullback P.syntaxData.sentenceNegation).obj T) ↔
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses (T : Tot C)).map
          (theoryDecision inverses P T hc)) :=
  subobject_inseparable_iff_no_total_extension inverses P T hc pointT hZ

example [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
    (pointT : Z ⟶ (T : Tot C)) :
    Inseparable (domain inverses T)
        (domain inverses ((Subobject.pullback P.syntaxData.sentenceNegation).obj T)) ↔
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses (T : Tot C)).map
          (theoryDecision inverses P T hc)) :=
  inseparable_iff_no_total_extension inverses P T hc pointT hZ

example (hpair : SubobjectInseparable a b) (θ : X ⟶ P.syntaxData.sentenceObject)
    (ha : a ≤ (Subobject.pullback θ).obj T)
    (hb : b ≤ (Subobject.pullback θ).obj
      ((Subobject.pullback P.syntaxData.sentenceNegation).obj T))
    (W : Subobject P.syntaxData.sentenceObject) (hTW : T ≤ W) (hcW : P.Consistent W)
    (pointW : Z ⟶ (W : Tot C)) :
    ¬ RestrictionRetraction.HasTotalExtension
      ((PartialSliceTheoryFamilies.constantFunctor inverses (W : Tot C)).map
        (theoryDecision inverses P W hcW)) :=
  no_total_extension_of_reduction inverses P a b hpair θ T W ha hb pointW hZ hTW hcW

#print axioms ConstantFamilyRetraction.terminalProductIso
#print axioms ConstantFamilyRetraction.constantTerminalIso
#print axioms ConstantFamilyRetraction.forward_naturality
#print axioms ConstantFamilyRetraction.pullbackConstantIso
#print axioms ConstantFamilyRetraction.point_mono
#print axioms ConstantFamilyRetraction.evaluation
#print axioms ConstantFamilyRetraction.retraction
#print axioms ConstantFamilyRetraction.evaluation_restriction
#print axioms RestrictionRetraction.recover_map
#print axioms RestrictionRetraction.faithful
#print axioms RestrictionRetraction.total_iff
#print axioms RestrictionRetraction.recover_extension
#print axioms RestrictionRetraction.hasTotalExtension_iff
#print axioms AssociatedCategory.evaluation
#print axioms AssociatedCategory.evaluation_spanPullback
#print axioms AssociatedCategory.retraction
#print axioms AssociatedCategory.constant_restriction
#print axioms AssociatedCategory.evaluation_restriction
#print axioms AssociatedCategory.constant_faithful
#print axioms AssociatedCategory.constant_total_iff
#print axioms AssociatedCategory.hasTotalExtension_iff
#print axioms BooleanPartialDecision.cover_mono
#print axioms BooleanPartialDecision.decision
#print axioms BooleanPartialDecision.positive_value
#print axioms BooleanPartialDecision.negative_value
#print axioms BooleanPartialDecision.domain_eq
#print axioms BooleanPartialDecision.total_iff
#print axioms BooleanPartialDecision.hasTotalExtension_iff_separator
#print axioms BooleanPartialDecision.inseparable_iff_noTotalExtension
#print axioms AssociatedCategory.theoryDecision_domain
#print axioms AssociatedCategory.incomplete_iff_decision_not_total
#print axioms AssociatedCategory.subobject_inseparable_iff_no_total_extension
#print axioms AssociatedCategory.inseparable_iff_no_total_extension
#print axioms AssociatedCategory.extension_inseparable
#print axioms AssociatedCategory.no_total_extension_of_reduction
