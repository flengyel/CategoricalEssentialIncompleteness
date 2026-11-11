/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedTranslation

/-! # An explicit named presentation of arithmetic formulas

The source keeps bound and free variable types separate. The target names
every binder explicitly. The comparison states preservation of semantics;
it does not identify these distinct syntax presentations by erasing names.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslation
open NamedArithmeticSignature

def truth : Formula := .equal zero zero
def falsity : Formula := .neg truth
def conjunction (φ ψ : Formula) : Formula := .neg (.imp φ (.neg ψ))
def disjunction (φ ψ : Formula) : Formula := .imp (.neg φ) ψ
def existential (name : ℕ) (φ : Formula) : Formula := .neg (.all name (.neg φ))

/-- The next unused name is recorded as the target binder, and the
extended variable context records exactly which source variable it binds. -/
def translateFormula : {n : ℕ} → ℕ → (Fin n → ℕ) → ArithmeticSemisentence n → Formula
  | _, _, _, .verum => truth
  | _, _, _, .falsum => falsity
  | _, _, names, .rel .eq children =>
      .equal (translateTerm names (children 0)) (translateTerm names (children 1))
  | _, _, names, .rel .lt children =>
      less (translateTerm names (children 0)) (translateTerm names (children 1))
  | _, _, names, .nrel .eq children =>
      .neg (.equal (translateTerm names (children 0)) (translateTerm names (children 1)))
  | _, _, names, .nrel .lt children =>
      .neg (less (translateTerm names (children 0)) (translateTerm names (children 1)))
  | _, next, names, .and φ ψ =>
      conjunction (translateFormula next names φ) (translateFormula next names ψ)
  | _, next, names, .or φ ψ =>
      disjunction (translateFormula next names φ) (translateFormula next names ψ)
  | _, next, names, .all φ =>
      .all next (translateFormula (next + 1) (Matrix.vecCons next names) φ)
  | _, next, names, .exs φ =>
      existential next (translateFormula (next + 1) (Matrix.vecCons next names) φ)

variable {K : Type w} [ORingStructure K]

@[simp] theorem holds_truth (ρ : ℕ → K) : truth.Holds functions relations ρ := by
  simp [truth,NamedFiniteSyntax.Formula.Holds]

@[simp] theorem not_holds_falsity (ρ : ℕ → K) : ¬ falsity.Holds functions relations ρ := by
  simp [falsity,NamedFiniteSyntax.Formula.Holds]

@[simp] theorem holds_conjunction (φ ψ : Formula) (ρ : ℕ → K) :
    (conjunction φ ψ).Holds functions relations ρ ↔
      φ.Holds functions relations ρ ∧ ψ.Holds functions relations ρ := by
  classical
  simp [conjunction,NamedFiniteSyntax.Formula.Holds]

@[simp] theorem holds_disjunction (φ ψ : Formula) (ρ : ℕ → K) :
    (disjunction φ ψ).Holds functions relations ρ ↔
      φ.Holds functions relations ρ ∨ ψ.Holds functions relations ρ := by
  classical
  simp only [disjunction,NamedFiniteSyntax.Formula.Holds]
  tauto

@[simp] theorem holds_existential (name : ℕ) (φ : Formula) (ρ : ℕ → K) :
    (existential name φ).Holds functions relations ρ ↔
      ∃ a : K, φ.Holds functions relations (Function.update ρ name a) := by
  classical
  simp [existential,NamedFiniteSyntax.Formula.Holds]

theorem namedContext_bound {n : ℕ} (next : ℕ) (names : Fin n → ℕ)
    (h : ∀ i, names i < next) :
    ∀ i, Matrix.vecCons next names i < next + 1 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa only [Matrix.cons_val_succ] using Nat.lt_succ_of_lt (h j)

omit [ORingStructure K] in
theorem update_namedContext {n : ℕ} (next : ℕ) (names : Fin n → ℕ)
    (h : ∀ i, names i < next) (ρ : ℕ → K) (a : K) :
    (fun i => Function.update ρ next a (Matrix.vecCons next names i)) =
      Matrix.vecCons a (fun i => ρ (names i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Matrix.cons_val_succ,Function.update_of_ne (Nat.ne_of_lt (h j))]

/-- Semantic comparison at an explicit fresh naming context, valid in an
arbitrary arithmetic structure K. -/
theorem holds_translateFormula {n : ℕ} (φ : ArithmeticSemisentence n) :
    ∀ (next : ℕ) (names : Fin n → ℕ), (∀ i, names i < next) →
      ∀ ρ : ℕ → K,
        (translateFormula next names φ).Holds functions relations ρ ↔
          φ.Evalb (s := Arithmetic.standardModel K) (fun i => ρ (names i)) := by
  induction φ with
  | verum =>
      intro next names h ρ
      change truth.Holds functions relations ρ ↔ True
      exact iff_true_intro (holds_truth ρ)
  | falsum =>
      intro next names h ρ
      change falsity.Holds functions relations ρ ↔ False
      exact iff_false_intro (not_holds_falsity ρ)
  | rel r children =>
      intro next names h ρ
      cases r with
      | eq =>
          change (translateTerm names (children 0)).evaluate functions ρ =
              (translateTerm names (children 1)).evaluate functions ρ ↔
            (children 0).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim =
              (children 1).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim
          rw [evaluate_translateTerm,evaluate_translateTerm]
      | lt =>
          change (less (translateTerm names (children 0)) (translateTerm names (children 1))).Holds
              functions relations ρ ↔
            (children 0).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim <
              (children 1).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim
          rw [holds_less,evaluate_translateTerm,evaluate_translateTerm]
  | nrel r children =>
      intro next names h ρ
      cases r with
      | eq =>
          change (¬ (translateTerm names (children 0)).evaluate functions ρ =
              (translateTerm names (children 1)).evaluate functions ρ) ↔
            ¬ (children 0).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim =
              (children 1).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim
          rw [evaluate_translateTerm,evaluate_translateTerm]
      | lt =>
          change (¬ (less (translateTerm names (children 0)) (translateTerm names (children 1))).Holds
              functions relations ρ) ↔
            ¬ (children 0).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim <
              (children 1).val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim
          rw [holds_less,evaluate_translateTerm,evaluate_translateTerm]
  | and φ ψ ihφ ihψ =>
      intro next names h ρ
      change (conjunction (translateFormula next names φ) (translateFormula next names ψ)).Holds
          functions relations ρ ↔
        φ.Evalb (s := Arithmetic.standardModel K) (fun i => ρ (names i)) ∧
          ψ.Evalb (s := Arithmetic.standardModel K) (fun i => ρ (names i))
      exact (holds_conjunction _ _ ρ).trans (and_congr (ihφ next names h ρ) (ihψ next names h ρ))
  | or φ ψ ihφ ihψ =>
      intro next names h ρ
      change (disjunction (translateFormula next names φ) (translateFormula next names ψ)).Holds
          functions relations ρ ↔
        φ.Evalb (s := Arithmetic.standardModel K) (fun i => ρ (names i)) ∨
          ψ.Evalb (s := Arithmetic.standardModel K) (fun i => ρ (names i))
      exact (holds_disjunction _ _ ρ).trans (or_congr (ihφ next names h ρ) (ihψ next names h ρ))
  | all φ ih =>
      intro next names h ρ
      change (∀ a : K, (translateFormula (next + 1) (Matrix.vecCons next names) φ).Holds
        functions relations (Function.update ρ next a)) ↔
          ∀ a : K, φ.Evalb (s := Arithmetic.standardModel K) (Matrix.vecCons a (fun i => ρ (names i)))
      apply forall_congr'
      intro a
      have he := ih (next + 1) (Matrix.vecCons next names)
        (namedContext_bound next names h) (Function.update ρ next a)
      rw [update_namedContext next names h ρ a] at he
      exact he
  | exs φ ih =>
      intro next names h ρ
      rw [translateFormula,holds_existential]
      change (∃ a : K, (translateFormula (next + 1) (Matrix.vecCons next names) φ).Holds
        functions relations (Function.update ρ next a)) ↔
          ∃ a : K, φ.Evalb (s := Arithmetic.standardModel K) (Matrix.vecCons a (fun i => ρ (names i)))
      apply exists_congr
      intro a
      have he := ih (next + 1) (Matrix.vecCons next names)
        (namedContext_bound next names h) (Function.update ρ next a)
      rw [update_namedContext next names h ρ a] at he
      exact he

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslation
