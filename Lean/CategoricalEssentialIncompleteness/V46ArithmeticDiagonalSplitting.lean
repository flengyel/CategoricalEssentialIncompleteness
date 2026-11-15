/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedGeneration
public import CategoricalEssentialIncompleteness.RestrictionSplitting

/-! # The diagonal predicates and the actual restriction splitting -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalSplitting

theorem predicateIdem_eq_of_models (C : Carrier) (a : Idem (omegaObject 𝗣𝗔))
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem a =
        setIdem {x : M | C.val.Evalb ![x]}) : predicateIdem 𝗣𝗔 C = a := by
  apply Idem.ext
  apply CodedHom.ext
  apply programClass_ext 𝗣𝗔
  intro M _ _ x y
  change SyntacticModel.programRelation 𝗣𝗔 M (predicateClass 𝗣𝗔 C) x y ↔ _
  rw [predicateClass_model]
  have he : (SyntacticModel.modelFunctor 𝗣𝗔 M).map a.hom =
      (setIdem {x : M | C.val.Evalb ![x]}).hom := congrArg Idem.hom (h M)
  have hm : y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map a.hom x ↔
      SyntacticModel.programRelation 𝗣𝗔 M a.hom.val x y :=
    ArithmeticDiagonalCodes.mem_model_relation M a.hom x y
  rw [he] at hm
  simpa only [mem_idem, support_setIdem, Set.mem_ofPred_eq] using hm

theorem alpha_idem : predicateIdem 𝗣𝗔 ArithmeticDiagonalCodes.alpha = ArithmeticDiagonalCodes.a0 :=
  predicateIdem_eq_of_models _ _ ArithmeticDiagonalCodes.model_a0

theorem beta_idem : predicateIdem 𝗣𝗔 ArithmeticDiagonalCodes.beta = ArithmeticDiagonalCodes.a1 :=
  predicateIdem_eq_of_models _ _ ArithmeticDiagonalCodes.model_a1

/-- Candidate complementary idempotents range over the full restriction splitting. -/
theorem source_pair_inseparable :
    Inseparable (SplitObject.includedIdem ArithmeticDiagonalCodes.a0)
      (SplitObject.includedIdem ArithmeticDiagonalCodes.a1) :=
  SplitObject.inclusion_inseparable ArithmeticDiagonalCodes.source_pair_inseparable

end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalSplitting
