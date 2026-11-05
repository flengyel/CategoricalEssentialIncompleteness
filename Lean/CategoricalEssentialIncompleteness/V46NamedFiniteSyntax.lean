/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Mathlib.Data.List.OfFn

/-! # Literal finite syntax with named binders

These external trees retain all names and ordered children. The comparison
with standard arithmetic postfix codes is a separate construction.
-/

universe u v w
namespace CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax

inductive Term (Sig : ℕ → Type u) (d : ℕ) : Type u
  | var (name : ℕ)
  | app (arity : Fin (d + 1)) (symbol : Sig arity.val)
      (children : Fin arity.val → Term Sig d)

inductive Formula (Sig : ℕ → Type u) (Rel : ℕ → Type v) (d : ℕ) : Type (max u v)
  | equal (left right : Term Sig d)
  | relation (arity : Fin (d + 1)) (symbol : Rel arity.val)
      (children : Fin arity.val → Term Sig d)
  | neg (body : Formula Sig Rel d)
  | imp (left right : Formula Sig Rel d)
  | all (name : ℕ) (body : Formula Sig Rel d)

variable {Sig : ℕ → Type u} {Rel : ℕ → Type v} {d : ℕ}

namespace Term

def freeVariables : Term Sig d → List ℕ
  | .var x => [x]
  | .app _ _ children => (List.ofFn (fun i => (children i).freeVariables)).flatten

@[simp] theorem mem_freeVariables_app (n : Fin (d + 1)) (f : Sig n.val)
    (children : Fin n.val → Term Sig d) (x : ℕ) :
    x ∈ (app n f children).freeVariables ↔ ∃ i, x ∈ (children i).freeVariables := by
  simp [freeVariables]

def substitute : Term Sig d → ℕ → Term Sig d → Term Sig d
  | .var y, x, replacement => if y = x then replacement else .var y
  | .app n f children, x, replacement => .app n f (fun i => (children i).substitute x replacement)

theorem substitute_absent (r : Term Sig d) (x : ℕ) (t : Term Sig d)
    (hx : x ∉ r.freeVariables) : r.substitute x t = r := by
  induction r with
  | var y => simp_all [freeVariables, substitute, eq_comm]
  | app n f children ih =>
      change app n f (fun i => _) = app n f children
      congr 1
      funext i
      exact ih i (fun h => hx ((mem_freeVariables_app n f children x).mpr ⟨i, h⟩))

variable {K : Type w}

def evaluate (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K) :
    Term Sig d → (ℕ → K) → K
  | .var x, assignment => assignment x
  | .app n f children, assignment =>
      functions n f (fun i => (children i).evaluate functions assignment)

variable (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)

theorem evaluate_congr (r : Term Sig d) {ρ τ : ℕ → K}
    (h : ∀ x, x ∈ r.freeVariables → ρ x = τ x) :
    r.evaluate functions ρ = r.evaluate functions τ := by
  induction r with
  | var x => exact h x (by simp [freeVariables])
  | app n f children ih =>
      apply congrArg (functions n f)
      funext i
      exact ih i (fun x hx => h x ((mem_freeVariables_app n f children x).mpr ⟨i, hx⟩))

theorem evaluate_update_absent (r : Term Sig d) (x : ℕ) (ρ : ℕ → K) (a : K)
    (hx : x ∉ r.freeVariables) :
    r.evaluate functions (Function.update ρ x a) = r.evaluate functions ρ := by
  apply evaluate_congr
  intro y hy
  have hne : y ≠ x := by
    intro he
    exact hx (he ▸ hy)
  simp [hne]

theorem evaluate_substitute (r t : Term Sig d) (x : ℕ) (ρ : ℕ → K) :
    (r.substitute x t).evaluate functions ρ =
      r.evaluate functions (Function.update ρ x (t.evaluate functions ρ)) := by
  induction r with
  | var y => by_cases h : y = x <;> simp [substitute, evaluate, h]
  | app n f children ih =>
      apply congrArg (functions n f)
      funext i
      exact ih i

end Term

namespace Formula

def freeVariables : Formula Sig Rel d → List ℕ
  | .equal r t => r.freeVariables ++ t.freeVariables
  | .relation _ _ children => (List.ofFn (fun i => (children i).freeVariables)).flatten
  | .neg body => body.freeVariables
  | .imp left right => left.freeVariables ++ right.freeVariables
  | .all x body => body.freeVariables.filter (fun y => y != x)

def substitute (x : ℕ) (replacement : Term Sig d) : Formula Sig Rel d → Option (Formula Sig Rel d)
  | .equal r t => some (.equal (r.substitute x replacement) (t.substitute x replacement))
  | .relation n p children => some (.relation n p (fun i => (children i).substitute x replacement))
  | .neg body => (body.substitute x replacement).map .neg
  | .imp left right => do
      let l ← left.substitute x replacement
      let r ← right.substitute x replacement
      pure (.imp l r)
  | .all y body =>
      if y = x then some (.all y body)
      else if x ∉ body.freeVariables ∨ y ∉ replacement.freeVariables then
        (body.substitute x replacement).map (.all y)
      else none

/-- This recursive condition has no reference to substitution success.
The equal-name branch does not demand admissibility of the body. -/
def FreeFor (x : ℕ) (replacement : Term Sig d) : Formula Sig Rel d → Prop
  | .equal _ _ => True
  | .relation _ _ _ => True
  | .neg body => body.FreeFor x replacement
  | .imp left right => left.FreeFor x replacement ∧ right.FreeFor x replacement
  | .all y body => y = x ∨ (y ≠ x ∧
      (x ∉ body.freeVariables ∨ y ∉ replacement.freeVariables) ∧ body.FreeFor x replacement)

theorem substitute_isSome_iff (φ : Formula Sig Rel d) (x : ℕ) (t : Term Sig d) :
    (φ.substitute x t).isSome = true ↔ φ.FreeFor x t := by
  induction φ with
  | equal r s => simp [substitute, FreeFor]
  | relation n p children => simp [substitute, FreeFor]
  | neg body ih => simpa [substitute, FreeFor] using ih
  | imp left right il ir =>
      cases hl : left.substitute x t <;> cases hr : right.substitute x t <;>
        simp_all [substitute, FreeFor]
  | all y body ih =>
      by_cases hy : y = x <;>
        by_cases hc : x ∉ body.freeVariables ∨ y ∉ t.freeVariables <;>
          simp_all [substitute, FreeFor]

variable {K : Type w}

def Holds (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)
    (relations : ∀ n : Fin (d + 1), Rel n.val → (Fin n.val → K) → Prop) :
    Formula Sig Rel d → (ℕ → K) → Prop
  | .equal r t, assignment => r.evaluate functions assignment = t.evaluate functions assignment
  | .relation n p children, assignment =>
      relations n p (fun i => (children i).evaluate functions assignment)
  | .neg body, assignment => ¬ body.Holds functions relations assignment
  | .imp left right, assignment =>
      left.Holds functions relations assignment → right.Holds functions relations assignment
  | .all x body, assignment => ∀ a : K, body.Holds functions relations (Function.update assignment x a)

end Formula
end CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax
