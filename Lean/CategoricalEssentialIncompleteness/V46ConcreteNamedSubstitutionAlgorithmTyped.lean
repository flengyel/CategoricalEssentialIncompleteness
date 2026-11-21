/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAlgorithm
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionRootClosure

/-!
PA typed preservation and branch equations for the primitive named substitution
algorithm and the independent structural free-for flag.
-/

@[expose] public section
noncomputable section
local instance primitiveNamedAlgorithmTypedDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedAlgorithmTypedModelDecidableEq : DecidableEq M := Classical.decEq M

local notation "A" => SyntaxPolynomial.termExpression V σ d
local notation "B" => SyntaxPolynomial.formulaExpression V π d
local notation "Tm" => Postfix.carrier false A B
local notation "Fm" => Postfix.carrier true A B
local notation "TP" => termPayloadCarrier V σ π d
local notation "FP" => formulaPayloadCarrier V σ π d

theorem substitutionPayload_carrier (formula : Bool) (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement])
    (hw : (Postfix.carrier formula A B).val.Evalb ![word]) :
    (if formula then FP else TP).val.Evalb ![substitutionPayload V σ π d x replacement word] := by
  let param := ⟪x,⟪replacement,freeVariables V σ π d replacement⟫⟫
  have hp : (Tm).val.Evalb ![π₁ (π₂ param)] := by simpa [param] using hrep
  exact Traversal.output_typed A B (termRootGraph V σ d) (formulaRootGraph V π d)
    (termRoot V σ d) (formulaRoot V π d) param TP FP
    (fun u hu => termRoot_carrier V σ π d param u hp hu) (formulaRoot_carrier V σ π d param) formula word hw

/-- Numerical term substitution preserves the named term predicate in PA, before
restriction to any stronger theory T. -/
theorem substitutionResult_term (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hw : (Tm).val.Evalb ![word]) :
    (Tm).val.Evalb ![substitutionResult V σ π d x replacement word] :=
  termPayload_result V σ π d _ (substitutionPayload_carrier V σ π d false x replacement word hrep hw)

/-- The formula traversal is total into the failure/success sum. -/
theorem substitutionResult_formula (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hw : (Fm).val.Evalb ![word]) :
    substitutionResult V σ π d x replacement word = 0 ∨ ∃ out : M,
      (Fm).val.Evalb ![out] ∧ substitutionResult V σ π d x replacement word = ok out := by
  have h := substitutionPayload_carrier V σ π d true x replacement word hrep hw
  simp [formulaPayloadCarrier] at h
  obtain ⟨old,fv,res,ff,he,_,_,hr⟩ := h
  have her : substitutionResult V σ π d x replacement word = res := by
    simpa [substitutionResult] using congrArg result he
  rcases hr with ⟨hz,_⟩ | ⟨out,ho,heq,_⟩
  · exact Or.inl (her.trans hz)
  · exact Or.inr ⟨out,by simpa using ho,her.trans heq⟩

/-- The independent free-for recursion agrees with the option tag. This is a proved
invariant of the numeric traversal, rather than its definition. -/
theorem substitutionFreeFor_success (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hw : (Fm).val.Evalb ![word]) :
    substitutionFreeFor V σ π d x replacement word =
      if π₂ (substitutionResult V σ π d x replacement word) = 1 then 1 else 0 :=
  formulaPayload_success V σ π d _
    (substitutionPayload_carrier V σ π d true x replacement word hrep hw)

theorem substitutionFreeFor_boolean (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hw : (Fm).val.Evalb ![word]) :
    substitutionFreeFor V σ π d x replacement word = 0 ∨
      substitutionFreeFor V σ π d x replacement word = 1 := by
  rw [substitutionFreeFor_success V σ π d x replacement word hrep hw]
  split_ifs <;> simp

theorem substitutionFreeFor_iff_success (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement]) (hw : (Fm).val.Evalb ![word]) :
    substitutionFreeFor V σ π d x replacement word = 1 ↔
      π₂ (substitutionResult V σ π d x replacement word) = 1 := by
  rw [substitutionFreeFor_success V σ π d x replacement word hrep hw]
  by_cases h : π₂ (substitutionResult V σ π d x replacement word) = 1 <;> simp [h]

/-- Complete simultaneous PA constructor equations for the paired
original/result computation, on the unchanged raw polynomial charts. -/
theorem substitutionPayload_term_constructor (x replacement u : M)
    (hu : (rawCarrier Tm Fm A).val.Evalb ![u]) :
    substitutionPayload V σ π d x replacement (constructor false A u) =
      termRoot V σ d ⟪x,⟪replacement,freeVariables V σ π d replacement⟫⟫
        (mapChildren (substitutionPayload V σ π d x replacement)
          (substitutionPayload V σ π d x replacement) A u) :=
  Traversal.output_term_constructor A B _ _ (termRoot V σ d) (formulaRoot V π d) _ u hu

theorem substitutionPayload_formula_constructor (x replacement u : M)
    (hu : (rawCarrier Tm Fm B).val.Evalb ![u]) :
    substitutionPayload V σ π d x replacement (constructor true B u) =
      formulaRoot V π d ⟪x,⟪replacement,freeVariables V σ π d replacement⟫⟫
        (mapChildren (substitutionPayload V σ π d x replacement)
          (substitutionPayload V σ π d x replacement) B u) :=
  Traversal.output_formula_constructor A B _ _ (termRoot V σ d) (formulaRoot V π d) _ u hu

/-- This PA equation explicitly retains the original recursively stored
body when the bound name equals x; no child-success premise occurs. -/
theorem substitutionResult_equal_binder (x replacement body : M)
    (hx : V.val.Evalb ![x]) (hb : (Fm).val.Evalb ![body]) :
    substitutionResult V σ π d x replacement (constructor true B ⟪⟪x,body⟫,1⟫) =
      ok (constructor true B ⟪⟪x,original (substitutionPayload V σ π d x replacement body)⟫,1⟫) := by
  have hu : (rawCarrier Tm Fm B).val.Evalb ![⟪⟪x,body⟫,1⟫] := by
    have hprod := (rawCarrier_product_eval Tm Fm (.coefficient V) .formula ⟪x,body⟫).mpr
      ⟨x,body,rfl,hx,hb⟩
    exact (rawCarrier_sum_eval Tm Fm (formulaLeft π d) (.product (.coefficient V) .formula)
      ⟪⟪x,body⟫,1⟫).mpr (Or.inr ⟨_,rfl,hprod⟩)
  unfold substitutionResult
  rw [substitutionPayload_formula_constructor V σ π d x replacement _ hu]
  simpa [SyntaxPolynomial.formulaExpression,mapChildren] using
    formulaRoot_equal_binder_result V π d x replacement (freeVariables V σ π d replacement)
      (substitutionPayload V σ π d x replacement body)

theorem substitutionFreeFor_equal_binder (x replacement body : M)
    (hx : V.val.Evalb ![x]) (hb : (Fm).val.Evalb ![body]) :
    substitutionFreeFor V σ π d x replacement (constructor true B ⟪⟪x,body⟫,1⟫) = 1 := by
  have hu : (rawCarrier Tm Fm B).val.Evalb ![⟪⟪x,body⟫,1⟫] := by
    have hprod := (rawCarrier_product_eval Tm Fm (.coefficient V) .formula ⟪x,body⟫).mpr
      ⟨x,body,rfl,hx,hb⟩
    exact (rawCarrier_sum_eval Tm Fm (formulaLeft π d) (.product (.coefficient V) .formula)
      ⟪⟪x,body⟫,1⟫).mpr (Or.inr ⟨_,rfl,hprod⟩)
  unfold substitutionFreeFor
  rw [substitutionPayload_formula_constructor V σ π d x replacement _ hu]
  simpa [SyntaxPolynomial.formulaExpression,mapChildren] using
    formulaRoot_equal_binder_freeFor V π d x replacement (freeVariables V σ π d replacement)
      (substitutionPayload V σ π d x replacement body)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
