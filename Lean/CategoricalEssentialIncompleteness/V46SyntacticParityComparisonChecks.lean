import CategoricalEssentialIncompleteness.V46SyntacticParityComparison

/-! # Exact even/odd model graphs for the source coproduct isomorphism -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.PartialSearchLift

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).hom (Sum.inl x) ↔
      y = 2 * x := mem_parity_encode_inl M x y

example (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).hom (Sum.inr x) ↔
      y = 2 * x + 1 := mem_parity_encode_inr M x y

example (x y : M) :
    Sum.inl y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).inv x ↔
      x = 2 * y := mem_parity_decode_inl M x y

example (x y : M) :
    Sum.inr y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).inv x ↔
      x = 2 * y + 1 := mem_parity_decode_inr M x y

example (C D : 𝚺₁.Semisentence 1)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (parityLift C D) x ↔
      (C.val.Evalb ![x] ∧ y = 2 * x + 1) ∨ (D.val.Evalb ![x] ∧ y = 2 * x) :=
  mem_parityLift M C D hd x y

example (C D : 𝚺₁.Semisentence 1) :
    parityLift C D ≫ (omegaCoprodIso 𝗣𝗔).inv = lift C D := parityLift_decode C D
