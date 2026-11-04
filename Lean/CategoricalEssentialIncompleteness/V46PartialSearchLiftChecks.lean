/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46PartialSearchLift

/-! # A source lift chosen before the interpreting model -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.PartialSearchLift

namespace CategoricalEssentialIncompleteness.V46.PartialSearchLift.StatementChecks

example (C D : 𝚺₁.Semisentence 1) :
    ∃ ell : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map ell)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {x : M | D.val.Evalb ![x]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map ell)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {x : M | C.val.Evalb ![x]} :=
  partial_lift C D

example (C D : 𝚺₁.Semisentence 1) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) (x : M) :
    (∃ y : M ⊕ M, y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) x) ↔
      C.val.Evalb ![x] ∨ D.val.Evalb ![x] :=
  model_lift_domain M C D hd x

example (C D : 𝚺₁.Semisentence 1) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) =
      (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) ≫
        ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
          (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom :=
  lift_comparison M C D

end CategoricalEssentialIncompleteness.V46.PartialSearchLift.StatementChecks
