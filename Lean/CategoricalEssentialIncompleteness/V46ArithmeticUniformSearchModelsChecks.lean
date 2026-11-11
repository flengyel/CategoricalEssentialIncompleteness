/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformSearchModels


/-! # Statement checks in `V46ArithmeticUniformSearchModelsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearchModelsChecks
open ArithmeticUniformSearch
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C C' : 𝚺₁.Semisentence 2) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x])) (x : M)
    (hC : C.val.Evalb ![e,x]) :
    Sum.inr x ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C C') (e,x) :=
  positive_lift_value M C C' e hd x hC
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C C' : 𝚺₁.Semisentence 2) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x])) (x : M)
    (hC' : C'.val.Evalb ![e,x]) :
    Sum.inl x ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C C') (e,x) :=
  negative_lift_value M C C' e hd x hC'
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C C' : 𝚺₁.Semisentence 2) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (hAlpha : ∀ x : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![x] → C.val.Evalb ![e,x])
    (hBeta : ∀ x : M, ArithmeticDiagonalCodes.beta.val.Evalb ![x] → C'.val.Evalb ![e,x])
    (n : M) (hn : n ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (diagonal C C') e) :
    ¬ C.val.Evalb ![e,n] ∧ ¬ C'.val.Evalb ![e,n] :=
  avoids_at M C C' e hd hAlpha hBeta n hn
end CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearchModelsChecks
