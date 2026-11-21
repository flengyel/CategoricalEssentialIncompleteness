/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofTranslation
public import CategoricalEssentialIncompleteness.V46NamedGammaSoundness

/-! # Arithmetic named syntax presented by source NNF formulas

Free names use a finite type. A quantifier closes precisely its original
name by a lifted source rewriting, so repeated binder names retain their
shadowing behavior. The presentation does not identify different names.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature

/-- All original names, including binder names, in their tree order. -/
def names : Formula → List ℕ
  | .equal r t => r.freeVariables ++ t.freeVariables
  | .relation _ _ children => (List.ofFn (fun i => (children i).freeVariables)).flatten
  | .neg φ => names φ
  | .imp φ ψ => names φ ++ names ψ
  | .all x φ => x :: names φ

def TermBound (n : ℕ) (r : Term) : Prop := ∀ x ∈ r.freeVariables, x < n

def Bound (n : ℕ) (φ : Formula) : Prop := ∀ x ∈ names φ, x < n

private theorem le_sum_of_mem {x : ℕ} (l : List ℕ) (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

def nameBound (φ : Formula) : ℕ := (names φ).sum + 1

theorem bound_nameBound (φ : Formula) : Bound (nameBound φ) φ := by
  intro x hx
  exact Nat.lt_succ_of_le (le_sum_of_mem (names φ) hx)

theorem bound_equal {n : ℕ} {r t : Term} :
    Bound n (.equal r t) ↔ TermBound n r ∧ TermBound n t := by
  simp only [Bound,names,TermBound,List.mem_append,or_imp,forall_and]

theorem bound_relation {n : ℕ} (k : Fin (bound+1)) (s : RelationSymbols k.val)
    (children : Fin k.val → Term) :
    Bound n (.relation k s children) ↔ ∀ i, TermBound n (children i) := by
  simp only [Bound,names,List.mem_flatten,List.mem_ofFn,TermBound]
  constructor
  · intro h i x hx
    exact h x ⟨(children i).freeVariables,⟨i,rfl⟩,hx⟩
  · intro h x hx
    rcases hx with ⟨l,⟨i,rfl⟩,hx⟩
    exact h i x hx

theorem bound_neg {n : ℕ} {φ : Formula} : Bound n (.neg φ) ↔ Bound n φ := Iff.rfl

theorem bound_imp {n : ℕ} {φ ψ : Formula} :
    Bound n (.imp φ ψ) ↔ Bound n φ ∧ Bound n ψ := by
  simp only [Bound,names,List.mem_append,or_imp,forall_and]

theorem bound_all {n x : ℕ} {φ : Formula} :
    Bound n (.all x φ) ↔ x < n ∧ Bound n φ := by
  simp only [Bound,names,List.mem_cons,or_imp,forall_and,forall_eq]

/-- A term retains each ordered arithmetic child and its original name.
The default branch is irrelevant whenever the name bound holds. -/
def term (n : ℕ) : Term → Semiterm ℒₒᵣ (Fin n) 0
  | .var x => if hx : x < n then .fvar ⟨x,hx⟩ else .func .zero Fin.elim0
  | .app k symbol children =>
      if h0 : k.val = 0 then
        if symbol.val = 0 then .func .zero Fin.elim0 else .func .one Fin.elim0
      else if h2 : k.val = 2 then
        if symbol.val = 0 then
          .func .add ![term n (children ⟨0,by omega⟩),term n (children ⟨1,by omega⟩)]
        else .func .mul ![term n (children ⟨0,by omega⟩),term n (children ⟨1,by omega⟩)]
      else .func .zero Fin.elim0

/-- Closing one name uses Foundation's bound-variable rewrite. -/
def bindName {n : ℕ} (x : Fin n) : Rew ℒₒᵣ (Fin n) 0 (Fin n) 1 :=
  Rew.bind Fin.elim0 (fun y => if y = x then .bvar 0 else .fvar y)

/-- The same closing operation removes that name from the free-name type.
This makes every remaining free name provably distinct from the binder. -/
def bindRemove {n : ℕ} (x : Fin n) : Rew ℒₒᵣ (Fin n) 0 {y : Fin n // y ≠ x} 1 :=
  Rew.bind Fin.elim0 (fun y => if h : y = x then .bvar 0 else .fvar ⟨y,h⟩)

def formula (n : ℕ) : Formula → Semiformula ℒₒᵣ (Fin n) 0
  | .equal r t => .rel .eq ![term n r,term n t]
  | .relation k symbol children =>
      if h : k.val = 2 then
        .rel .lt ![term n (children ⟨0,by omega⟩),term n (children ⟨1,by omega⟩)]
      else ⊥
  | .neg φ => ∼formula n φ
  | .imp φ ψ => formula n φ 🡒 formula n ψ
  | .all x φ => if hx : x < n then ∀¹ (bindName ⟨x,hx⟩ ▹ formula n φ) else formula n φ

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
