/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedSeparator
public import CategoricalEssentialIncompleteness.V46SignedSubobjectIncompleteness
public import CategoricalEssentialIncompleteness.V46SyntacticNullaryPresentations

/-! # Essential incompleteness of the arithmetic diagonal signed theory -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedEssential
open ArithmeticSignedAtoms
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)

theorem diagonal_disjoint : positiveSubobject ⊓ negativeSubobject = ⊥ := by
  let I := positiveSubobject ⊓ negativeSubobject
  apply PredicateModelSubobjects.eq_bot_of_models_empty 𝗣𝗔 I
  intro M _ _ z
  let a : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (I : PredicateCategory 𝗣𝗔) ArithmeticDiagonalCodes.alpha :=
    Subobject.ofLE I positiveSubobject inf_le_left ≫
      (Subobject.underlyingIso (numberInclusion ArithmeticDiagonalCodes.alpha)).hom
  let b : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (I : PredicateCategory 𝗣𝗔) ArithmeticDiagonalCodes.beta :=
    Subobject.ofLE I negativeSubobject inf_le_right ≫
      (Subobject.underlyingIso (numberInclusion ArithmeticDiagonalCodes.beta)).hom
  have ha : a ≫ numberInclusion ArithmeticDiagonalCodes.alpha = I.arrow := by
    dsimp only [a]
    erw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]
  have hb : b ≫ numberInclusion ArithmeticDiagonalCodes.beta = I.arrow := by
    dsimp only [b]
    erw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]
  have hpa := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 M a
    (numberInclusion ArithmeticDiagonalCodes.alpha) (𝟙 _) I.arrow
    (by simpa only [Category.id_comp] using ha) z
  have hpb := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 M b
    (numberInclusion ArithmeticDiagonalCodes.beta) (𝟙 _) I.arrow
    (by simpa only [Category.id_comp] using hb) z
  have hva := congrArg Subtype.val hpa
  have hvb := congrArg Subtype.val hpb
  simp only [numberInclusion_value, Functor.map_id_apply] at hva hvb
  exact ArithmeticDiagonalCodes.output_disjoint ((F 𝗣𝗔 M).map I.arrow z).val
    ⟨hva ▸ ((F 𝗣𝗔 M).map a z).property, hvb ▸ ((F 𝗣𝗔 M).map b z).property⟩

theorem diagonal_inseparable : SubobjectInseparable positiveSubobject negativeSubobject :=
  ⟨diagonal_disjoint, ArithmeticSignedSeparator.no_separator⟩

/-- Every consistent closed extension is incomplete. -/
theorem essentially_incomplete {V : PredicateCategory 𝗣𝗔} (F : NullaryPresentations V) :
    (F.presentation N).EssentiallyIncomplete
      (SignedFirstOrder.theory F positiveSubobject negativeSubobject) :=
  SignedFirstOrder.essential_incomplete_of_subobject_inseparable F positiveSubobject negativeSubobject
    diagonal_inseparable (ArithmeticSignedTheoryTruth.signed_theory_consistent F)

/-- The extension quantifier ranges over all closed theories of the presentation. -/
theorem every_consistent_extension_incomplete {V : PredicateCategory 𝗣𝗔}
    (F : NullaryPresentations V) (U : (F.presentation N).Theories)
    (hExt : (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val ≤ U.val)
    (consistent : (F.presentation N).Consistent U.val) :
    ¬ (F.presentation N).Complete U.val :=
  (essentially_incomplete F).2 U hExt consistent

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedEssential
