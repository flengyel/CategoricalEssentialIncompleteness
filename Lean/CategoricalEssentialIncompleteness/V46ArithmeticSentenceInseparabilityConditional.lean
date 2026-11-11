/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalRealization
public import CategoricalEssentialIncompleteness.V46SyntacticParityComparison

/-! # Recursive reversed conditionals with actual partial source lifts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FailureOfComposition FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability

/-- Positive membership selects the second numerical summand. -/
def reversedCode (g : ℕ → Bool) (n : ℕ) : ℕ :=
  cond (g n) (2*n+1) (2*n)

def reversedConditional (g : ℕ → Bool) :
    PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ) :=
  fun n => Part.some (cond (g n) (Sum.inr n) (Sum.inl n))

theorem reversedCode_computable (g : ℕ → Bool) (hg : Computable g) :
    Computable (reversedCode g) :=
  Computable.cond hg
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 2) .id) (.const 1))
    (Primrec.nat_mul.to_comp.comp (.const 2) .id)

/-- Totality belongs to the standard conditional. No source totality is
claimed or needed for its chosen index. -/
theorem reversedConditional_total (g : ℕ → Bool) : isTotal (reversedConditional g) := by
  change rst (reversedConditional g) = 𝟙 (PartialFun.of ℕ)
  apply PFun.ext
  intro x y
  simp [reversedConditional,mem_rst,mem_id]

theorem reversedConditional_fiber0 (g : ℕ → Bool) :
    Idem.pull (reversedConditional g)
      (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) = setIdem {n | g n = false} := by
  apply support_injective
  ext n
  rw [support_pull,support_setIdem]
  change (∃ y : ℕ ⊕ ℕ, y ∈ reversedConditional g n ∧
    y ∈ support (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ))) ↔ g n = false
  cases he : g n <;>
    simp [reversedConditional,he,Part.mem_some_iff,PartialSearchLift.mem_support_summand0]

theorem reversedConditional_fiber1 (g : ℕ → Bool) :
    Idem.pull (reversedConditional g)
      (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) = setIdem {n | g n = true} := by
  apply support_injective
  ext n
  rw [support_pull,support_setIdem]
  change (∃ y : ℕ ⊕ ℕ, y ∈ reversedConditional g n ∧
    y ∈ support (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ))) ↔ g n = true
  cases he : g n <;>
    simp [reversedConditional,he,Part.mem_some_iff,PartialSearchLift.mem_support_summand1]

/-- A recursive reversed conditional has an actual program-class lift.
The proof uses its parity-coded total recursive function and the fixed
source coproduct decoder; the resulting source morphism may be partial. -/
theorem exists_reversedConditional_index (g : ℕ → Bool) (hg : Computable g) :
    ∃ q : ℕ,
      (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map
        (arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) q) =
      reversedConditional g ≫ ((SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).comparison
        (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom := by
  obtain ⟨j,hj⟩ := ClassicalPrograms.represents_partrec
    (fun n => Part.some (reversedCode g n)) (reversedCode_computable g hg).partrec
  let ℓ := j ≫ (omegaCoprodIso 𝗣𝗔).inv
  have hℓ : (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map ℓ = reversedConditional g := by
    apply PFun.ext
    intro x y
    rw [show ℓ = j ≫ (omegaCoprodIso 𝗣𝗔).inv from rfl,Functor.map_comp,mem_comp]
    rw [show (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map j =
      (fun n => Part.some (reversedCode g n)) from hj]
    simp only [Part.mem_some_iff,exists_eq_left]
    cases y with
    | inl m =>
        rw [PartialSearchLift.mem_parity_decode_inl]
        cases he : g x <;> simp [reversedCode,reversedConditional,he] <;>
          first | exact ⟨fun h => congrArg Sum.inl h.symm, fun h => (Sum.inl.inj h).symm⟩ | omega
    | inr m =>
        rw [PartialSearchLift.mem_parity_decode_inr]
        cases he : g x <;> simp [reversedCode,reversedConditional,he] <;>
          first | exact ⟨fun h => congrArg Sum.inr h.symm, fun h => (Sum.inr.inj h).symm⟩ | omega
  obtain ⟨q,hq⟩ := exists_arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) ℓ
  refine ⟨q,?_⟩
  have hc : ((SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).comparison
      (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom = 𝟙 _ :=
    SyntacticModel.model_comparison_eq_id 𝗣𝗔 ℕ _ _
  rw [hq,hc]
  exact hℓ.trans (Category.comp_id (reversedConditional g)).symm

/-- For any recursive set, the concrete source index lifts its reversed
conditional on the complementary target partial identities. -/
theorem recursive_set_conditional (C : Set ℕ) (hC : ComputablePred (· ∈ C)) :
    ∃ (s : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ)) (q : ℕ),
      isTotal s ∧
      Idem.pull s (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) = setIdem Cᶜ ∧
      Idem.pull s (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) = setIdem C ∧
      (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map
        (arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) q) =
        s ≫ ((SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).comparison
          (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom := by
  obtain ⟨g,hg,he⟩ := ComputablePred.computable_iff.mp hC
  have htrue : {n | g n = true} = C := by
    ext n
    exact (congrFun he n).symm.to_iff
  have hfalse : {n | g n = false} = Cᶜ := by
    ext n
    change (g n = false) ↔ n ∉ C
    rw [← htrue]
    change (g n = false) ↔ ¬ (g n = true)
    cases g n <;> decide
  obtain ⟨q,hq⟩ := exists_reversedConditional_index g hg
  exact ⟨reversedConditional g,q,reversedConditional_total g,
    (reversedConditional_fiber0 g).trans (congrArg setIdem hfalse),
    (reversedConditional_fiber1 g).trans (congrArg setIdem htrue),hq⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparability
