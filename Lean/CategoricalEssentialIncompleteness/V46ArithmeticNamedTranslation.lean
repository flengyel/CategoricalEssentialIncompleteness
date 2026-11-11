/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticSignature
public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Mathlib.Tactic.FinCases

/-! # The literal named arithmetic signature and arithmetic semantics

The arithmetic structure interpreting a formula is independent of the
standard arithmetic structure used to interpret its symbol predicates.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslation
open NamedArithmeticSignature

/-- An explicit context assigns a name to each source bound variable.
No binder names are erased from the target syntax. -/
def translateTerm {n : ℕ} (names : Fin n → ℕ) : ArithmeticSemiterm Empty n → Term
  | .bvar i => .var (names i)
  | .fvar e => nomatch e
  | .func .zero _ => zero
  | .func .one _ => one
  | .func .add children =>
      add (translateTerm names (children 0)) (translateTerm names (children 1))
  | .func .mul children =>
      mul (translateTerm names (children 0)) (translateTerm names (children 1))

theorem translateTerm_freeVariables {n : ℕ} (names : Fin n → ℕ)
    (t : ArithmeticSemiterm Empty n) (x : ℕ)
    (hx : x ∈ (translateTerm names t).freeVariables) : ∃ i, names i = x := by
  induction t with
  | bvar i =>
      have he : x = names i := by
        simpa [translateTerm,NamedFiniteSyntax.Term.freeVariables] using hx
      exact ⟨i,he.symm⟩
  | fvar e => exact e.elim
  | func f children ih =>
      cases f with
      | zero => simp [translateTerm] at hx
      | one => simp [translateTerm] at hx
      | add =>
          rcases (List.mem_append.mp (by simpa [translateTerm] using hx)) with hx | hx
          · exact ih 0 hx
          · exact ih 1 hx
      | mul =>
          rcases (List.mem_append.mp (by simpa [translateTerm] using hx)) with hx | hx
          · exact ih 0 hx
          · exact ih 1 hx

variable {K : Type w} [ORingStructure K]

/-- Interpret the actual numerical function-symbol predicates in K. -/
def functions : (n : Fin (bound + 1)) → FunctionSymbols n.val → (Fin n.val → K) → K
  | ⟨0,_⟩, symbol, _ => if symbol.val = 0 then 0 else 1
  | ⟨1,_⟩, symbol, _ => False.elim
      ((functionSymbols_other_eval (M := ℕ) 1 (by decide) (by decide) symbol.val) symbol.property)
  | ⟨2,_⟩, symbol, arguments =>
      if symbol.val = 0 then arguments 0 + arguments 1 else arguments 0 * arguments 1
  | ⟨n+3,h⟩, _, _ => False.elim (by change n + 3 < 3 at h; omega)

/-- Equality is interpreted by the built-in equality constructor. -/
def relations : (n : Fin (bound + 1)) → RelationSymbols n.val → (Fin n.val → K) → Prop
  | ⟨0,_⟩, symbol, _ => False.elim
      ((relationSymbols_other_eval (M := ℕ) 0 (by decide) symbol.val) symbol.property)
  | ⟨1,_⟩, symbol, _ => False.elim
      ((relationSymbols_other_eval (M := ℕ) 1 (by decide) symbol.val) symbol.property)
  | ⟨2,_⟩, _, arguments => arguments 0 < arguments 1
  | ⟨n+3,h⟩, _, _ => False.elim (by change n + 3 < 3 at h; omega)

@[simp] theorem functions_zero (arguments : Fin 0 → K) :
    functions ⟨0,by decide⟩ zeroSymbol arguments = 0 := by
  simp [functions,zeroSymbol]

@[simp] theorem functions_one (arguments : Fin 0 → K) :
    functions ⟨0,by decide⟩ oneSymbol arguments = 1 := by
  simp [functions,oneSymbol]

@[simp] theorem functions_add (arguments : Fin 2 → K) :
    functions ⟨2,by decide⟩ addSymbol arguments = arguments 0 + arguments 1 := by
  simp [functions,addSymbol]

@[simp] theorem functions_mul (arguments : Fin 2 → K) :
    functions ⟨2,by decide⟩ mulSymbol arguments = arguments 0 * arguments 1 := by
  simp [functions,mulSymbol]

@[simp] theorem relations_less (arguments : Fin 2 → K) :
    relations ⟨2,by decide⟩ ltSymbol arguments ↔ arguments 0 < arguments 1 := by
  simp [relations]

@[simp] theorem evaluate_zero (ρ : ℕ → K) :
    zero.evaluate functions ρ = 0 := by
  exact functions_zero _

@[simp] theorem evaluate_one (ρ : ℕ → K) :
    one.evaluate functions ρ = 1 := by
  exact functions_one _

@[simp] theorem evaluate_add (r t : Term) (ρ : ℕ → K) :
    (add r t).evaluate functions ρ = r.evaluate functions ρ + t.evaluate functions ρ := by
  simp [add,NamedFiniteSyntax.Term.evaluate]

@[simp] theorem evaluate_mul (r t : Term) (ρ : ℕ → K) :
    (mul r t).evaluate functions ρ = r.evaluate functions ρ * t.evaluate functions ρ := by
  simp [mul,NamedFiniteSyntax.Term.evaluate]

@[simp] theorem holds_less (r t : Term) (ρ : ℕ → K) :
    (less r t).Holds functions relations ρ ↔
      r.evaluate functions ρ < t.evaluate functions ρ := by
  simp [less,NamedFiniteSyntax.Formula.Holds]

/-- The explicit source-variable/name context gives the semantic
comparison, rather than an equality of the two syntax presentations. -/
theorem evaluate_translateTerm {n : ℕ} (names : Fin n → ℕ)
    (t : ArithmeticSemiterm Empty n) (ρ : ℕ → K) :
    (translateTerm names t).evaluate functions ρ = t.val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim := by
  induction t with
  | bvar i => rfl
  | fvar e => exact e.elim
  | func f children ih =>
      cases f with
      | zero => exact evaluate_zero ρ
      | one => exact evaluate_one ρ
      | add =>
          change (add (translateTerm names (children 0)) (translateTerm names (children 1))).evaluate
            functions ρ = _ + _
          rw [evaluate_add,ih 0,ih 1]
      | mul =>
          change (mul (translateTerm names (children 0)) (translateTerm names (children 1))).evaluate
            functions ρ = _ * _
          rw [evaluate_mul,ih 0,ih 1]

/-- The value of the chosen numeral recurrence in an arbitrary arithmetic
structure. No algebraic axioms for K or identification with the code model
are needed. -/
@[simp] theorem evaluate_numeral (n : ℕ) (ρ : ℕ → K) :
    (numeral n).evaluate functions ρ =
      Nat.rec (0 : K) (fun _ previous => previous + 1) n := by
  induction n with
  | zero => exact evaluate_zero ρ
  | succ n ih =>
      rw [numeral_succ,evaluate_add,ih,evaluate_one]

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslation
