/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AssociatedSliceCoordinates

/-! # Essential incompleteness in the associated category -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionSubobjects AssociatedCategory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)]
local instance checkSliceRegular (U : Tot C) : Regular (Over U) := RegularSlices.regular U
local instance checkSliceExtensive (U : Tot C) : FinitaryExtensive (Over U) :=
  RegularSlices.finitaryExtensive U
local instance checkConstantLimits (U : Tot C) : PreservesFiniteLimits (constantFamilyFunctor U) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U
local instance checkActualLimits (U : Tot C) :
    PreservesFiniteLimits (AssociatedSliceCoordinates.actualConstant U) :=
  preservesFiniteLimits_of_natIso (AssociatedSliceCoordinates.comparison U)
variable (inverses : MonoInverses C) {V Z : Tot C} (P : FirstOrderPresentation V)
variable (Q : (U : Tot C) → AssociatedClosedTheories.SliceProofs P U)
variable (hQ : ∀ U W, IsInitial (Q U W))
variable (logicalTheorem : Z ⟶ P.syntaxData.sentenceObject) (hZ : IsTerminal Z)
variable (factors : ∀ U : P.Theories, P.Consistent U.val →
  ∃ point : Z ⟶ (U.val : Tot C), point ≫ U.val.arrow = logicalTheorem)

section FullQuantifiers
variable [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]

example (U : P.Theories) (hcU : P.Consistent U.val) :
    (P.EssentiallyIncomplete U ↔
      AssociatedClosedTheories.Consistent P (U.val : Tot C)
        (FiniteLimitSubobjects.object (constantFamilyFunctor (U.val : Tot C)) U.val) ∧
      ∀ W : Subobject (constantFamily (U.val : Tot C) P.syntaxData.sentenceObject),
        FirstOrderReflection.generated (Q (U.val : Tot C)) W = W →
        FiniteLimitSubobjects.object (constantFamilyFunctor (U.val : Tot C)) U.val ≤ W →
        W ⊓ (Subobject.pullback
          ((constantFamilyFunctor (U.val : Tot C)).map P.syntaxData.sentenceNegation)).obj W = ⊥ →
        W ⊔ (Subobject.pullback
          ((constantFamilyFunctor (U.val : Tot C)).map P.syntaxData.sentenceNegation)).obj W ≠ ⊤) ∧
    (¬ P.Complete U.val ↔
      ¬ isTotal ((PartialSliceTheoryFamilies.constantFunctor inverses (U.val : Tot C)).map
        (theoryDecision inverses P U.val hcU))) ∧
    (Inseparable (domain inverses U.val)
        (domain inverses ((Subobject.pullback P.syntaxData.sentenceNegation).obj U.val)) ↔
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses (U.val : Tot C)).map
          (theoryDecision inverses P U.val hcU))) := by
  have h := associated_incompleteness inverses P Q hQ logicalTheorem hZ factors U hcU
  obtain ⟨point, _⟩ := factors U hcU
  refine ⟨?_, h.2.1, inseparable_iff_no_total_extension inverses P U.val hcU point hZ⟩
  constructor
  · intro he
    have hs := h.1.mp he
    refine ⟨hs.1, ?_⟩
    intro W hW hUW hcW hcompW
    exact hs.2 ⟨W, hW⟩ hUW hcW hcompW
  · intro hs
    apply h.1.mpr
    refine ⟨hs.1, ?_⟩
    intro W hUW hcW hcompW
    exact hs.2 W.val W.property hUW hcW hcompW
end FullQuantifiers

example {X : Tot C} (a b : Subobject X) (hab : SubobjectInseparable a b)
    (θ : X ⟶ P.syntaxData.sentenceObject) (t : Subobject P.syntaxData.sentenceObject)
    (ha : a ≤ (Subobject.pullback θ).obj t)
    (hb : b ≤ (Subobject.pullback θ).obj
      ((Subobject.pullback P.syntaxData.sentenceNegation).obj t)) :
    ∀ U : P.Theories, t ≤ U.val → (hcU : P.Consistent U.val) →
      AssociatedClosedTheories.EssentiallyIncomplete P (U.val : Tot C) (Q (U.val : Tot C))
        (AssociatedClosedTheories.constantTheory P (U.val : Tot C)
          (Q (U.val : Tot C)) (hQ (U.val : Tot C)) U) ∧
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses (U.val : Tot C)).map
          (theoryDecision inverses P U.val hcU)) := by
  intro U htU hcU
  exact associated_reduction inverses P Q hQ logicalTheorem hZ factors a b hab θ t ha hb U htU hcU

example {A : Tot C} (a : A ⟶ P.syntaxData.sentenceObject) :
    ((FirstOrderReflection.presentationGeneration P.proofs P.initial).obj (Over.mk a)).val =
      FirstOrderReflection.generated P.proofs (imageSubobject a) := rfl

section ArbitrarySlice
variable (U : Tot C) (point : Z ⟶ U)

example (W : FirstOrderReflection.Theory (Q U)) :
    P.Theories := AssociatedClosedTheories.evaluationTheory P U (Q U) (hQ U) point hZ W

example (W : FirstOrderReflection.Theory (Q U))
    (hc : AssociatedClosedTheories.Consistent P U W.val)
    (hcomp : AssociatedClosedTheories.Complete P U W.val) :
    P.Consistent (AssociatedClosedTheories.evaluationTheory P U (Q U) (hQ U) point hZ W).val ∧
      P.Complete (AssociatedClosedTheories.evaluationTheory P U (Q U) (hQ U) point hZ W).val :=
  ⟨SliceSubobjectPredicates.evaluate_consistency point hZ P.syntaxData.sentenceNegation W.val hc,
    SliceSubobjectPredicates.evaluate_completeness point hZ
      P.syntaxData.sentenceNegation W.val hcomp⟩
end ArbitrarySlice

section ActualCoordinates
variable (U : Tot C)

example : constantFamilyFunctor U ≅ AssociatedSliceCoordinates.actualConstant U :=
  AssociatedSliceCoordinates.comparison U

example {S : Tot C} (T : Subobject S) :
    (Subobject.map ((AssociatedSliceCoordinates.comparison U).hom.app S)).obj
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) T) =
      FiniteLimitSubobjects.object (AssociatedSliceCoordinates.actualConstant U) T :=
  AssociatedSliceCoordinates.theory_value U T

example (T : P.Theories) :
    (PartialSliceTheoryFamilies.sourceTheory inverses T.val.arrow).hom =
      PartialMaps.ofTotal ((AssociatedSliceCoordinates.actualConstant (T.val : Tot C)).map
        T.val.arrow) :=
  AssociatedSliceCoordinates.actual_map inverses (T.val : Tot C) T.val.arrow

example (point : Z ⟶ U) {X Y : PartialMaps.Par (Over U)} (f : X.obj ⟶ Y.obj) :
    (AssociatedCategory.evaluation inverses point).map (PartialMaps.ofTotal f) =
      (((Over.pullback point).map f).left).hom :=
  AssociatedSliceCoordinates.evaluation_total inverses point f
end ActualCoordinates

#print axioms AssociatedSliceCoordinates.comparison
#print axioms AssociatedSliceCoordinates.theory_value
#print axioms AssociatedSliceCoordinates.actual_map
#print axioms AssociatedSliceCoordinates.evaluation_total
#print axioms SliceSubobjectPredicates.orderIso
#print axioms SliceSubobjectPredicates.underlying_pullback
#print axioms SliceSubobjectPredicates.underlying_constant
#print axioms SliceSubobjectPredicates.constant_consistency
#print axioms SliceSubobjectPredicates.constant_completeness
#print axioms SliceSubobjectPredicates.evaluate_consistency
#print axioms SliceSubobjectPredicates.evaluate_completeness
#print axioms SliceSubobjectPredicates.evaluate_constant
#print axioms SliceSubobjectPredicates.evaluation_square
#print axioms SliceSubobjectPredicates.evaluate_eq_retraction
#print axioms SliceBaseChangeGeometry.ordinaryRetraction
#print axioms RetractedRuleComparison.translation
#print axioms RetractedClosedTheories.closed_back
#print axioms AssociatedClosedTheories.constantTheory
#print axioms AssociatedClosedTheories.evaluationTheory
#print axioms AssociatedClosedTheories.essential_incomplete_iff
#print axioms AssociatedCategory.essential_incomplete_of_reduction
#print axioms AssociatedCategory.associated_incompleteness
#print axioms AssociatedCategory.associated_reduction
