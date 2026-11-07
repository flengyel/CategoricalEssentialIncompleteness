/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring
import CategoricalEssentialIncompleteness.ClassicalRecursionCategory
import CategoricalEssentialIncompleteness.ClassicalSplitMaps

/-! # The printed universal program's actual classical diagonal pair -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness

/-- The universal map is the denotation of the printed universal index. -/
def tauRec : PCategoryStruct.nearProd ClassicalPrograms.U ClassicalPrograms.U ⟶ ClassicalPrograms.U :=
  ClassicalPrograms.Q.map ArithmeticDiagonalCodes.sourceTau

theorem tauRec_isTuring : RecursionCategory.IsTuringMorphism tauRec := by
  intro V f
  obtain ⟨f,hf⟩ := ClassicalPrograms.exists_source f
  obtain ⟨g,hg,he⟩ := ArithmeticDiagonalCodes.sourceTau_isTuring V.base f
  refine ⟨ClassicalPrograms.Q.map g,ClassicalPrograms.quotientRangeFunctor.map_total g hg,?_⟩
  have hh := congrArg (fun k => ClassicalPrograms.Q.map k) he
  simpa [Functor.map_comp,ClassicalPrograms.Q_product,Functor.map_id,
    ClassicalPrograms.Q_obj_base,ClassicalPrograms.Q_product_obj,ClassicalPrograms.U,tauRec,hf] using hh

def aRec : Idem ClassicalPrograms.U := diagonal0 tauRec ClassicalPrograms.parityIso
def bRec : Idem ClassicalPrograms.U := diagonal1 tauRec ClassicalPrograms.parityIso

private theorem quotient_summand0 :
    ClassicalPrograms.quotientRangeFunctor.mapIdem
      (summand0 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)) =
      summand0 ClassicalPrograms.U ClassicalPrograms.U := by
  apply Idem.ext
  apply ClassicalPrograms.J.map_injective
  change ((SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).mapIdem
    (summand0 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔))).hom =
    (ClassicalPrograms.inclusionRangeFunctor.mapIdem
      (summand0 ClassicalPrograms.U ClassicalPrograms.U)).hom
  exact congrArg Idem.hom ((ArithmeticDiagonalCodes.model_summand0 ℕ).trans ClassicalPrograms.J_summand0.symm)

private theorem quotient_summand1 :
    ClassicalPrograms.quotientRangeFunctor.mapIdem
      (summand1 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)) =
      summand1 ClassicalPrograms.U ClassicalPrograms.U := by
  apply Idem.ext
  apply ClassicalPrograms.J.map_injective
  change ((SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).mapIdem
    (summand1 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔))).hom =
    (ClassicalPrograms.inclusionRangeFunctor.mapIdem
      (summand1 ClassicalPrograms.U ClassicalPrograms.U)).hom
  exact congrArg Idem.hom ((ArithmeticDiagonalCodes.model_summand1 ℕ).trans ClassicalPrograms.J_summand1.symm)

/-- This compares the actual diagonal restrictions, including the program
and the parity coproduct map, before using their arithmetic supports. -/
theorem quotient_a0 :
    ClassicalPrograms.quotientRangeFunctor.mapIdem ArithmeticDiagonalCodes.a0 = aRec := by
  unfold ArithmeticDiagonalCodes.a0 aRec diagonal0
  rw [RangeFunctor.map_pull,quotient_summand0]
  congr 1
  simp only [Functor.map_comp]
  rfl

theorem quotient_a1 :
    ClassicalPrograms.quotientRangeFunctor.mapIdem ArithmeticDiagonalCodes.a1 = bRec := by
  unfold ArithmeticDiagonalCodes.a1 bRec diagonal1
  rw [RangeFunctor.map_pull,quotient_summand1]
  congr 1
  simp only [Functor.map_comp]
  rfl

theorem aRec_standard :
    ClassicalPrograms.inclusionRangeFunctor.mapIdem aRec =
      setIdem {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} := by
  rw [← quotient_a0]
  exact ArithmeticDiagonalCodes.model_a0 ℕ

theorem bRec_standard :
    ClassicalPrograms.inclusionRangeFunctor.mapIdem bRec =
      setIdem {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} := by
  rw [← quotient_a1]
  exact ArithmeticDiagonalCodes.model_a1 ℕ

/-- The categorical diagonal theorem is applied to the printed map's
actual classical denotation. No arithmetic incompleteness result is used. -/
theorem diagonal_inseparable : Inseparable aRec bRec :=
  range_functor_lifting ClassicalPrograms.inclusionRangeFunctor tauRec tauRec_isTuring
    ClassicalPrograms.parityIso ClassicalPrograms.inclusion_nonzero
    (section_lifting_of_choice ClassicalPrograms.inclusionRangeFunctor ClassicalPrograms.U)

abbrev includedA : Idem ClassicalPrograms.parameterObject := SplitObject.includedIdem aRec
abbrev includedB : Idem ClassicalPrograms.parameterObject := SplitObject.includedIdem bRec

theorem included_inseparable : Inseparable includedA includedB :=
  SplitObject.inclusion_inseparable diagonal_inseparable

theorem includedA_support :
    ClassicalPrograms.splitSupport includedA =
      {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} := by
  change support (ClassicalPrograms.inclusionRangeFunctor.mapIdem aRec) = _
  rw [aRec_standard,support_setIdem]

theorem includedB_support :
    ClassicalPrograms.splitSupport includedB =
      {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} := by
  change support (ClassicalPrograms.inclusionRangeFunctor.mapIdem bRec) = _
  rw [bRec_standard,support_setIdem]

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness
