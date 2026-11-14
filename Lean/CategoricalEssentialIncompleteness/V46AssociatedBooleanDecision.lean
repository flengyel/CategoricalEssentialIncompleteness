/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AssociatedEvaluation
public import CategoricalEssentialIncompleteness.V46BooleanPartialDecision
public import CategoricalEssentialIncompleteness.V46SignedSubobjectIncompleteness
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectInseparability

/-! # Boolean partial morphisms of theories in associated partial slices -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AssociatedCategory

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)]
variable (inverses : MonoInverses C) {V : Tot C} (P : FirstOrderPresentation V)
variable (T : Subobject P.syntaxData.sentenceObject) (hc : P.Consistent T)

def theoryDecision : P.syntaxData.sentenceObject.obj ⟶ (Two (Tot C)).obj :=
  BooleanPartialDecision.decision inverses T
    ((Subobject.pullback P.syntaxData.sentenceNegation).obj T) hc

omit [Splits C] in
theorem theoryDecision_domain : rst (theoryDecision inverses P T hc) =
    (domain inverses (T ⊔ (Subobject.pullback P.syntaxData.sentenceNegation).obj T)).hom :=
  BooleanPartialDecision.domain_eq inverses _ _ hc

omit [Splits C] in
theorem theoryDecision_true : T.arrow.hom ≫ theoryDecision inverses P T hc =
    (Two.constant (T : Tot C) true).hom :=
  BooleanPartialDecision.positive_value inverses _ _ hc

omit [Splits C] in
theorem theoryDecision_false :
    ((Subobject.pullback P.syntaxData.sentenceNegation).obj T).arrow.hom ≫
        theoryDecision inverses P T hc =
      (Two.constant ((Subobject.pullback P.syntaxData.sentenceNegation).obj T : Tot C) false).hom :=
  BooleanPartialDecision.negative_value inverses _ _ hc

variable {Z U : Tot C} (point : Z ⟶ U) (hZ : IsTerminal Z)

include point hZ in
theorem incomplete_iff_decision_not_total :
    ¬ P.Complete T ↔
      ¬ isTotal ((PartialSliceTheoryFamilies.constantFunctor inverses U).map
        (theoryDecision inverses P T hc)) := by
  exact (not_congr ((constant_total_iff inverses point hZ _).trans
    (BooleanPartialDecision.total_iff inverses _ _ hc))).symm

include point hZ in
theorem subobject_inseparable_iff_no_total_extension :
    SubobjectInseparable T ((Subobject.pullback P.syntaxData.sentenceNegation).obj T) ↔
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses U).map
          (theoryDecision inverses P T hc)) :=
  (BooleanPartialDecision.inseparable_iff_noTotalExtension inverses _ _ hc).trans
    (noTotalExtension_iff inverses point hZ _).symm

variable [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]

include point hZ in
theorem inseparable_iff_no_total_extension :
    Inseparable (domain inverses T)
        (domain inverses ((Subobject.pullback P.syntaxData.sentenceNegation).obj T)) ↔
      ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses U).map
          (theoryDecision inverses P T hc)) :=
  (RestrictionSubobjects.inseparable_iff inverses _ _).trans
    (subobject_inseparable_iff_no_total_extension inverses P T hc point hZ)

end CategoricalEssentialIncompleteness.V46.AssociatedCategory
