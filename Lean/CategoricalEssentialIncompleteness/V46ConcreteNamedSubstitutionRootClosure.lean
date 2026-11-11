/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionCarriers

/-! PA carrier preservation for the actual substitution roots, including the
branch which succeeds at an equal binder despite recursive body failure. -/

@[expose] public section
noncomputable section
local instance primitiveNamedRootClosureDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedRootClosureModelDecidableEq : DecidableEq M := Classical.decEq M

local notation "A" => SyntaxPolynomial.termExpression V σ d
local notation "B" => SyntaxPolynomial.formulaExpression V π d
local notation "Tm" => Postfix.carrier false A B
local notation "Fm" => Postfix.carrier true A B
local notation "TP" => termPayloadCarrier V σ π d
local notation "FP" => formulaPayloadCarrier V σ π d
local notation "LV" => SyntacticLists.listCarrier V

theorem termRoot_carrier (param u : M)
    (hrep : (Tm).val.Evalb ![π₁ (π₂ param)])
    (hu : (rawCarrier TP FP A).val.Evalb ![u]) :
    (TP).val.Evalb ![termRoot V σ d param u] := by
  have ho : (Tm).val.Evalb ![constructor false A (mapChildren original original A u)] :=
    Postfix.term_constructor_carrier A B _ (originalMap_carrier V σ π d A u hu)
  have hv : (LV).val.Evalb ![freeVarsTermRoot σ d param (mapChildren occurrences occurrences A u)] :=
    freeVarsTermRoot_carrier V σ d param _ (occurrencesMap_carrier V σ π d A u hu)
  have hr : (Tm).val.Evalb ![constructor false A (mapChildren result successfulValue A u)] :=
    Postfix.term_constructor_carrier A B _ (successfulMap_carrier V σ π d A u hu
      (termExpression_allChildren V σ d success u))
  simp only [termRoot,termPayloadCarrier_payload]
  refine ⟨ho,hv,?_,True.intro⟩
  by_cases htag : π₂ u = 0
  · by_cases hname : π₁ u = π₁ param
    · simpa [htag,hname] using hrep
    · simpa [htag,hname] using ho
  · simpa [htag] using hr

private theorem quantifierBody_carrier (X Y W : Carrier) (q : RawPolynomial) (u : M)
    (hu : (rawCarrier X Y (.sum q (.product (.coefficient W) .formula))).val.Evalb ![u])
    (htag : π₂ u ≠ 0) : Y.val.Evalb ![π₂ (π₁ u)] := by
  rcases (rawCarrier_sum_eval X Y q (.product (.coefficient W) .formula) u).mp hu with
    ⟨v,rfl,hraw⟩ | ⟨v,rfl,hraw⟩
  · simp at htag
  · obtain ⟨y,body,rfl,_,hbody⟩ :=
      (rawCarrier_product_eval X Y (.coefficient W) .formula v).mp hraw
    simpa [rawCarrier] using hbody

theorem formulaRoot_carrier (param u : M)
    (hu : (rawCarrier TP FP B).val.Evalb ![u]) :
    (FP).val.Evalb ![formulaRoot V π d param u] := by
  let old := constructor true B (mapChildren original original B u)
  let fv := freeVarsFormulaRoot π d param (mapChildren occurrences occurrences B u)
  let rebuilt := constructor true B (mapChildren result successfulValue B u)
  have ho : (Fm).val.Evalb ![old] :=
    Postfix.formula_constructor_carrier A B _ (originalMap_carrier V σ π d B u hu)
  have hv : (LV).val.Evalb ![fv] :=
    freeVarsFormulaRoot_carrier V π d param _ (occurrencesMap_carrier V σ π d B u hu)
  have hr : allChildren (fun _ : M => 1) success B u = 1 → (Fm).val.Evalb ![rebuilt] := by
    intro hs
    exact Postfix.formula_constructor_carrier A B _ (successfulMap_carrier V σ π d B u hu hs)
  have hflags := allChildren_flags V σ π d B u hu
  simp only [formulaRoot,formulaPayloadCarrier_payload]
  refine ⟨ho,hv,?_⟩
  by_cases htag : π₂ u = 0
  · by_cases hs : allChildren (fun _ : M => 1) success B u = 1
    · have hfs : allChildren (fun _ : M => 1) freeFor B u = 1 := hflags.trans hs
      apply Or.inr
      refine ⟨rebuilt,hr hs,?_,?_⟩ <;> simp [htag,hs,hfs,rebuilt]
    · have hfs : allChildren (fun _ : M => 1) freeFor B u ≠ 1 := by simpa [hflags] using hs
      exact Or.inl ⟨by simp [htag,hs],by simp [htag,hfs]⟩
  · by_cases hname : π₁ (π₁ u) = π₁ param
    · apply Or.inr
      refine ⟨old,ho,?_,?_⟩ <;> simp [htag,hname,old]
    · have hb : (FP).val.Evalb ![π₂ (π₁ u)] :=
        quantifierBody_carrier TP FP V (formulaLeft π d) u hu htag
      have hfbody := formulaPayload_success V σ π d (π₂ (π₁ u)) hb
      by_cases hc : capture param u = 1 ∧ success (π₂ (π₁ u)) = 1
      · have hall : allChildren (fun _ : M => 1) success B u = 1 := by
          simp [SyntaxPolynomial.formulaExpression,allChildren,htag,hc.2]
        apply Or.inr
        refine ⟨rebuilt,hr hall,?_,?_⟩ <;> simp [htag,hname,hc,hfbody,rebuilt]
      · exact Or.inl ⟨by simp [htag,hname,hc],by simp [htag,hname,hfbody,hc]⟩

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
