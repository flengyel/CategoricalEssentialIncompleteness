/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedTotal

/-! # The printed split diagonal generators -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedSplitGenerators
open ArithmeticSignedAtoms ArithmeticDiagonalSplitting

local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)

theorem number_idem : predicateIdem 𝗣𝗔 N = ⊤ := by
  apply predicateIdem_eq_of_models
  intro M _ _
  rw [(SyntacticModel.modelRangeFunctor 𝗣𝗔 M).map_top]
  apply Idem.ext
  funext x
  apply Part.ext
  intro y
  simp only [Idem.top_hom, mem_id, mem_idem, support_setIdem,
    PrintedObjectCoding.Number, memberFormula_omega_eval]
  change y = x ↔ True ∧ y = x
  exact ⟨fun h => ⟨trivial, h⟩, And.right⟩

theorem number_object : (interpretedObject 𝗣𝗔 N).obj =
    (splittingInclusion (C := CodedProgramCategory 𝗣𝗔)).obj (omegaObject 𝗣𝗔) := by
  change (⟨omegaObject 𝗣𝗔, predicateIdem 𝗣𝗔 N⟩ : SplitObject _) = ⟨omegaObject 𝗣𝗔, ⊤⟩
  rw [number_idem]

theorem alpha_object : (interpretedObject 𝗣𝗔 ArithmeticDiagonalCodes.alpha).obj =
    (⟨omegaObject 𝗣𝗔, ArithmeticDiagonalCodes.a0⟩ : SplitObject _) := by
  change (⟨omegaObject 𝗣𝗔, predicateIdem 𝗣𝗔 ArithmeticDiagonalCodes.alpha⟩ : SplitObject _) = _
  rw [alpha_idem]

theorem beta_object : (interpretedObject 𝗣𝗔 ArithmeticDiagonalCodes.beta).obj =
    (⟨omegaObject 𝗣𝗔, ArithmeticDiagonalCodes.a1⟩ : SplitObject _) := by
  change (⟨omegaObject 𝗣𝗔, predicateIdem 𝗣𝗔 ArithmeticDiagonalCodes.beta⟩ : SplitObject _) = _
  rw [beta_idem]

theorem inclusion_underlying (C : PredicateCategory 𝗣𝗔) :
    ((realization 𝗣𝗔).map (numberInclusion C)).hom.hom = (predicateIdem 𝗣𝗔 C).hom := by
  rfl

theorem positive_underlying :
    ((realization 𝗣𝗔).map (numberInclusion ArithmeticDiagonalCodes.alpha)).hom.hom =
      ArithmeticDiagonalCodes.a0.hom := by
  rw [inclusion_underlying, alpha_idem]

theorem negative_underlying :
    ((realization 𝗣𝗔).map (numberInclusion ArithmeticDiagonalCodes.beta)).hom.hom =
      ArithmeticDiagonalCodes.a1.hom := by
  rw [inclusion_underlying, beta_idem]

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedSplitGenerators
