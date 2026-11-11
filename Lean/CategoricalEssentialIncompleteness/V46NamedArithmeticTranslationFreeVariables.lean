/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedFormulaTranslation

/-! The explicit naming context bounds all free names of a translated
formula. This is a finite external syntax statement; internal PA numeral
substitution and sentence-range proofs remain separate. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslation
open NamedArithmeticSignature

private theorem less_freeVariables (s t : Term) :
    (less s t).freeVariables = s.freeVariables ++ t.freeVariables := by
  simp [less,NamedFiniteSyntax.Formula.freeVariables,List.ofFn_succ]

private theorem drop_bound_name {n : ℕ} (next : ℕ) (names : Fin n → ℕ) (x : ℕ)
    (hne : x ≠ next) (h : ∃ i, Matrix.vecCons next names i = x) : ∃ i, names i = x := by
  obtain ⟨i,hi⟩ := h
  have hh : ∀ j, Matrix.vecCons next names j = x → ∃ i, names i = x := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · intro he
      exact False.elim (hne (by simpa using he.symm))
    · intro he
      exact ⟨k,by simpa only [Matrix.cons_val_succ] using he⟩
  exact hh i hi

/-- Binding introduces the chosen explicit name, and filtering that name
removes its contribution before returning to the original context. No
semantic interpretation or bound-variable erasure is used. -/
theorem translateFormula_freeVariables {n : ℕ} (φ : ArithmeticSemisentence n) :
    ∀ (next : ℕ) (names : Fin n → ℕ) (x : ℕ),
      x ∈ (translateFormula next names φ).freeVariables → ∃ i, names i = x := by
  induction φ with
  | verum =>
    intro next names x hx
    simp [translateFormula,truth,NamedFiniteSyntax.Formula.freeVariables] at hx
  | falsum =>
    intro next names x hx
    simp [translateFormula,falsity,truth,NamedFiniteSyntax.Formula.freeVariables] at hx
  | rel r children =>
    intro next names x hx
    cases r with
    | eq =>
      change x ∈ (translateTerm names (children 0)).freeVariables ++
        (translateTerm names (children 1)).freeVariables at hx
      rcases List.mem_append.mp hx with h | h
      · exact translateTerm_freeVariables names (children 0) x h
      · exact translateTerm_freeVariables names (children 1) x h
    | lt =>
      change x ∈ (less (translateTerm names (children 0)) (translateTerm names (children 1))).freeVariables at hx
      rw [less_freeVariables] at hx
      rcases List.mem_append.mp hx with h | h
      · exact translateTerm_freeVariables names (children 0) x h
      · exact translateTerm_freeVariables names (children 1) x h
  | nrel r children =>
    intro next names x hx
    cases r with
    | eq =>
      change x ∈ (translateTerm names (children 0)).freeVariables ++
        (translateTerm names (children 1)).freeVariables at hx
      rcases List.mem_append.mp hx with h | h
      · exact translateTerm_freeVariables names (children 0) x h
      · exact translateTerm_freeVariables names (children 1) x h
    | lt =>
      change x ∈ (less (translateTerm names (children 0)) (translateTerm names (children 1))).freeVariables at hx
      rw [less_freeVariables] at hx
      rcases List.mem_append.mp hx with h | h
      · exact translateTerm_freeVariables names (children 0) x h
      · exact translateTerm_freeVariables names (children 1) x h
  | and φ ψ ihφ ihψ =>
    intro next names x hx
    change x ∈ (translateFormula next names φ).freeVariables ++
      (translateFormula next names ψ).freeVariables at hx
    rcases List.mem_append.mp hx with h | h
    · exact ihφ next names x h
    · exact ihψ next names x h
  | or φ ψ ihφ ihψ =>
    intro next names x hx
    change x ∈ (translateFormula next names φ).freeVariables ++
      (translateFormula next names ψ).freeVariables at hx
    rcases List.mem_append.mp hx with h | h
    · exact ihφ next names x h
    · exact ihψ next names x h
  | all φ ih =>
    intro next names x hx
    change x ∈ (translateFormula (next+1) (Matrix.vecCons next names) φ).freeVariables.filter
      (fun y => y != next) at hx
    obtain ⟨hm,hne⟩ := List.mem_filter.mp hx
    exact drop_bound_name next names x (by simpa using hne)
      (ih (next+1) (Matrix.vecCons next names) x hm)
  | exs φ ih =>
    intro next names x hx
    change x ∈ (translateFormula (next+1) (Matrix.vecCons next names) φ).freeVariables.filter
      (fun y => y != next) at hx
    obtain ⟨hm,hne⟩ := List.mem_filter.mp hx
    exact drop_bound_name next names x (by simpa using hne)
      (ih (next+1) (Matrix.vecCons next names) x hm)

theorem translateUnary_freeVariables (α : ArithmeticSemisentence 1) (x : ℕ)
    (hx : x ∈ (translateFormula 1 ![0] α).freeVariables) : x = 0 := by
  obtain ⟨i,hi⟩ := translateFormula_freeVariables α 1 ![0] x hx
  fin_cases i
  simpa using hi.symm

/-- Empty source contexts produce literal named sentences. -/
theorem translateSentence_freeVariables (φ : ArithmeticSentence) (next : ℕ) :
    (translateFormula next ![] φ).freeVariables = [] := by
  cases hv : (translateFormula next ![] φ).freeVariables with
  | nil => rfl
  | cons x xs =>
    have hx : x ∈ (translateFormula next ![] φ).freeVariables := by rw [hv]; simp
    obtain ⟨i,_⟩ := translateFormula_freeVariables φ next ![] x hx
    exact Fin.elim0 i

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslation
