/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixEncoding

/-! The fixed arithmetic signature, with literal variable names and
ordered children. Equality is the built-in formula constructor; the
single ordinary relation symbol is strict order. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature

abbrev bound : ℕ := 2
abbrev variableSymbols : Carrier := NamedPostfixEncoding.variableCarrier

def functionSymbols (n : ℕ) : Carrier :=
  if n = 0 ∨ n = 2 then .mkSigma “c. c = 0 ∨ c = 1” else .mkSigma “c. 0 = 1”

def relationSymbols (n : ℕ) : Carrier :=
  if n = 2 then .mkSigma “c. c = 1” else .mkSigma “c. 0 = 1”

section Models
variable {M : Type} [ORingStructure M]

@[simp] theorem variables_eval (x : M) : variableSymbols.val.Evalb ![x] := by
  simp [variableSymbols,NamedPostfixEncoding.variableCarrier]

@[simp] theorem functionSymbols_zero_eval (x : M) :
    (functionSymbols 0).val.Evalb ![x] ↔ x = 0 ∨ x = 1 := by simp [functionSymbols]
@[simp] theorem functionSymbols_two_eval (x : M) :
    (functionSymbols 2).val.Evalb ![x] ↔ x = 0 ∨ x = 1 := by simp [functionSymbols]
@[simp] theorem relationSymbols_two_eval (x : M) :
    (relationSymbols 2).val.Evalb ![x] ↔ x = 1 := by simp [relationSymbols]

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
@[simp] theorem functionSymbols_other_eval (n : ℕ) (hn : n ≠ 0) (hn' : n ≠ 2) (x : M) :
    ¬ (functionSymbols n).val.Evalb ![x] := by simp [functionSymbols,hn,hn']
@[simp] theorem relationSymbols_other_eval (n : ℕ) (hn : n ≠ 2) (x : M) :
    ¬ (relationSymbols n).val.Evalb ![x] := by simp [relationSymbols,hn]
end Models

abbrev FunctionSymbols := NamedPostfixEncoding.Symbols functionSymbols
abbrev RelationSymbols := NamedPostfixEncoding.Symbols relationSymbols
abbrev Term := NamedFiniteSyntax.Term FunctionSymbols bound
abbrev Formula := NamedFiniteSyntax.Formula FunctionSymbols RelationSymbols bound

def zeroSymbol : FunctionSymbols 0 := ⟨0,by simp⟩
def oneSymbol : FunctionSymbols 0 := ⟨1,by simp⟩
def addSymbol : FunctionSymbols 2 := ⟨0,by simp⟩
def mulSymbol : FunctionSymbols 2 := ⟨1,by simp⟩
def ltSymbol : RelationSymbols 2 := ⟨1,by simp⟩

/-- These are syntax constructors, not arithmetic operations on word codes. -/
def zero : Term := .app ⟨0,by decide⟩ zeroSymbol Fin.elim0
def one : Term := .app ⟨0,by decide⟩ oneSymbol Fin.elim0
def add (s t : Term) : Term := .app ⟨2,by decide⟩ addSymbol ![s,t]
def mul (s t : Term) : Term := .app ⟨2,by decide⟩ mulSymbol ![s,t]
def less (s t : Term) : Formula := .relation ⟨2,by decide⟩ ltSymbol ![s,t]

@[simp] theorem zero_freeVariables : zero.freeVariables = [] := by
  simp [zero,NamedFiniteSyntax.Term.freeVariables]
@[simp] theorem one_freeVariables : one.freeVariables = [] := by
  simp [one,NamedFiniteSyntax.Term.freeVariables]
@[simp] theorem add_freeVariables (s t : Term) : (add s t).freeVariables = s.freeVariables ++ t.freeVariables := by
  simp [add,NamedFiniteSyntax.Term.freeVariables,List.ofFn_succ]
@[simp] theorem mul_freeVariables (s t : Term) : (mul s t).freeVariables = s.freeVariables ++ t.freeVariables := by
  simp [mul,NamedFiniteSyntax.Term.freeVariables,List.ofFn_succ]

/-- Literal arithmetic numerals use zero, one and binary addition. -/
def numeral : ℕ → Term
  | 0 => zero
  | n + 1 => add (numeral n) one

@[simp] theorem numeral_zero : numeral 0 = zero := rfl
@[simp] theorem numeral_succ (n : ℕ) : numeral (n+1) = add (numeral n) one := rfl
@[simp] theorem numeral_freeVariables (n : ℕ) : (numeral n).freeVariables = [] := by
  induction n with
  | zero => exact zero_freeVariables
  | succ n ih => simp [numeral,ih]

abbrev termPolynomial := NamedPostfixEncoding.termPolynomial functionSymbols bound
abbrev formulaPolynomial := NamedPostfixEncoding.formulaPolynomial relationSymbols bound
abbrev termCode : Term → ℕ := NamedPostfixEncoding.termCode
abbrev formulaCode : Formula → ℕ := NamedPostfixEncoding.formulaCode

end CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
