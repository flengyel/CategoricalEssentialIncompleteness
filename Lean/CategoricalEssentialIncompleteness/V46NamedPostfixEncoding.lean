/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedFiniteSyntax
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! # Standard postfix codes of literal named finite syntax -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding

def variableCarrier : Carrier := .mkSigma “x. 0 = 0”

def Symbols (σ : ℕ → Carrier) (n : ℕ) := {c : ℕ // (σ n).val.Evalb ![c]}

def termPolynomial (σ : ℕ → Carrier) (d : ℕ) : RawPolynomial :=
  SyntaxPolynomial.termExpression variableCarrier σ d

def formulaPolynomial (π : ℕ → Carrier) (d : ℕ) : RawPolynomial :=
  SyntaxPolynomial.formulaExpression variableCarrier π d

/-- The ordered finite power convention is the manuscript's convention:
zero is terminal, one is the child itself, higher powers associate left. -/
def childTuple : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | 1, f => f 0
  | n + 2, f => Arithmetic.pair (childTuple (n + 1) (fun i => f i.castSucc))
      (f (Fin.last (n + 1)))

/-- The finite coproduct is left associated and includes the nullary branch. -/
def arityInput : (d : ℕ) → Fin (d + 1) → ℕ → ℕ
  | 0, _, payload => payload
  | d + 1, k, payload => Fin.lastCases
      (Arithmetic.pair payload 1)
      (fun j => Arithmetic.pair (arityInput d j payload) 0) k

variable {σ π : ℕ → Carrier} {d : ℕ}

def termCode : NamedFiniteSyntax.Term (Symbols σ) d → ℕ
  | .var x => constructor false (termPolynomial σ d) (Arithmetic.pair x 0)
  | .app k f children => constructor false (termPolynomial σ d)
      (Arithmetic.pair (arityInput d k
        (Arithmetic.pair f.val (childTuple k.val (fun i => termCode (children i))))) 1)

def equalInput (r t : ℕ) : ℕ :=
  Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair r t) 0) 0) 0) 0

def relationInput (d : ℕ) (k : Fin (d + 1)) (p : ℕ) (children : Fin k.val → ℕ) : ℕ :=
  Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
    (arityInput d k (Arithmetic.pair p (childTuple k.val children))) 1) 0) 0) 0

def negInput (body : ℕ) : ℕ := Arithmetic.pair (Arithmetic.pair (Arithmetic.pair body 1) 0) 0

def impInput (left right : ℕ) : ℕ :=
  Arithmetic.pair (Arithmetic.pair (Arithmetic.pair left right) 1) 0

def allInput (name body : ℕ) : ℕ := Arithmetic.pair (Arithmetic.pair name body) 1

def formulaCode : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d → ℕ
  | .equal r t => constructor true (formulaPolynomial π d)
      (equalInput (termCode r) (termCode t))
  | .relation k p children => constructor true (formulaPolynomial π d)
      (relationInput d k p.val (fun i => termCode (children i)))
  | .neg body => constructor true (formulaPolynomial π d)
      (negInput (formulaCode body))
  | .imp left right => constructor true (formulaPolynomial π d)
      (impInput (formulaCode left) (formulaCode right))
  | .all x body => constructor true (formulaPolynomial π d)
      (allInput x (formulaCode body))

theorem childTuple_member (X Y : Carrier) (n : ℕ) (f : Fin n → ℕ)
    (h : ∀ i, X.val.Evalb ![f i]) :
    (rawCarrier X Y (SyntaxPolynomial.power .term n)).val.Evalb ![childTuple n f] := by
  induction n with
  | zero => simp [SyntaxPolynomial.power, childTuple, rawCarrier]
  | succ n ih =>
      cases n with
      | zero => simpa [SyntaxPolynomial.power, childTuple, rawCarrier] using h 0
      | succ n =>
          rw [SyntaxPolynomial.power, childTuple, rawCarrier_product_eval]
          exact ⟨_, _, rfl, ih (fun i => f i.castSucc) (fun i => h i.castSucc), h (Fin.last (n + 1))⟩

theorem arityInput_member (X Y : Carrier) (σ : ℕ → Carrier) (d : ℕ)
    (k : Fin (d + 1)) (payload : ℕ)
    (h : (rawCarrier X Y (.product (.coefficient (σ k.val))
      (SyntaxPolynomial.power .term k.val))).val.Evalb ![payload]) :
    (rawCarrier X Y (SyntaxPolynomial.constructors σ d)).val.Evalb ![arityInput d k payload] := by
  induction d with
  | zero =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      exact h
  | succ d ih =>
      refine Fin.lastCases ?_ (fun j => ?_) k h
      · intro hl
        rw [arityInput, Fin.lastCases_last, SyntaxPolynomial.constructors, rawCarrier_sum_eval]
        exact Or.inr ⟨payload, rfl, hl⟩
      · intro hl
        rw [arityInput, Fin.lastCases_castSucc, SyntaxPolynomial.constructors, rawCarrier_sum_eval]
        exact Or.inl ⟨arityInput d j payload, rfl, ih j hl⟩

theorem left_member (X Y : Carrier) (p q : RawPolynomial) (u : ℕ)
    (h : (rawCarrier X Y p).val.Evalb ![u]) :
    (rawCarrier X Y (.sum p q)).val.Evalb ![Arithmetic.pair u 0] :=
  (rawCarrier_sum_eval X Y p q _).mpr (Or.inl ⟨u, rfl, h⟩)

theorem right_member (X Y : Carrier) (p q : RawPolynomial) (u : ℕ)
    (h : (rawCarrier X Y q).val.Evalb ![u]) :
    (rawCarrier X Y (.sum p q)).val.Evalb ![Arithmetic.pair u 1] :=
  (rawCarrier_sum_eval X Y p q _).mpr (Or.inr ⟨u, rfl, h⟩)

theorem termCode_member (π : ℕ → Carrier) (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![termCode r] := by
  induction r with
  | var x =>
      apply Postfix.term_constructor_carrier
      apply left_member
      simp [rawCarrier, variableCarrier]
  | app k f children ih =>
      apply Postfix.term_constructor_carrier
      apply right_member
      apply arityInput_member
      rw [rawCarrier_product_eval]
      exact ⟨f.val, _, rfl, f.property, childTuple_member _ _ k.val _ ih⟩

theorem formulaCode_member (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![formulaCode φ] := by
  induction φ with
  | equal r t =>
      apply Postfix.formula_constructor_carrier
      apply left_member
      apply left_member
      apply left_member
      apply left_member
      simp only [SyntaxPolynomial.power]
      rw [rawCarrier_product_eval]
      exact ⟨termCode r, termCode t, rfl, termCode_member π r, termCode_member π t⟩
  | relation k p children =>
      apply Postfix.formula_constructor_carrier
      apply left_member
      apply left_member
      apply left_member
      apply right_member
      apply arityInput_member
      rw [rawCarrier_product_eval]
      exact ⟨p.val, _, rfl, p.property,
        childTuple_member _ _ k.val _ (fun i => termCode_member π (children i))⟩
  | neg body ih =>
      apply Postfix.formula_constructor_carrier
      apply left_member
      apply left_member
      apply right_member
      exact ih
  | imp left right il ir =>
      apply Postfix.formula_constructor_carrier
      apply left_member
      apply right_member
      simp only [SyntaxPolynomial.power]
      rw [rawCarrier_product_eval]
      exact ⟨formulaCode left, formulaCode right, rfl, il, ir⟩
  | all x body ih =>
      apply Postfix.formula_constructor_carrier
      apply right_member
      rw [rawCarrier_product_eval]
      exact ⟨x, formulaCode body, rfl, by simp [rawCarrier, variableCarrier], ih⟩

def termInput : NamedFiniteSyntax.Term (Symbols σ) d → ℕ
  | .var x => Arithmetic.pair x 0
  | .app k f children => Arithmetic.pair (arityInput d k
      (Arithmetic.pair f.val (childTuple k.val (fun i => termCode (children i))))) 1

def formulaInput : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d → ℕ
  | .equal r t => equalInput (termCode r) (termCode t)
  | .relation k p children => relationInput d k p.val (fun i => termCode (children i))
  | .neg body => negInput (formulaCode body)
  | .imp left right => impInput (formulaCode left) (formulaCode right)
  | .all x body => allInput x (formulaCode body)

theorem termCode_root (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    termCode r = constructor false (termPolynomial σ d) (termInput r) := by
  cases r <;> rfl

theorem formulaCode_root (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    formulaCode φ = constructor true (formulaPolynomial π d) (formulaInput φ) := by
  cases φ <;> rfl

theorem termInput_member (π : ℕ → Carrier) (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    (rawCarrier (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d))
      (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d))
      (termPolynomial σ d)).val.Evalb ![termInput r] := by
  cases r with
  | var x =>
      apply left_member
      simp [rawCarrier, variableCarrier]
  | app k f children =>
      apply right_member
      apply arityInput_member
      rw [rawCarrier_product_eval]
      exact ⟨f.val, _, rfl, f.property,
        childTuple_member _ _ k.val _ (fun i => termCode_member π (children i))⟩

theorem formulaInput_member (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (rawCarrier (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d))
      (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d))
      (formulaPolynomial π d)).val.Evalb ![formulaInput φ] := by
  cases φ with
  | equal r t =>
      apply left_member
      apply left_member
      apply left_member
      apply left_member
      simp only [SyntaxPolynomial.power]
      rw [rawCarrier_product_eval]
      exact ⟨termCode r, termCode t, rfl, termCode_member π r, termCode_member π t⟩
  | relation k p children =>
      apply left_member
      apply left_member
      apply left_member
      apply right_member
      apply arityInput_member
      rw [rawCarrier_product_eval]
      exact ⟨p.val, _, rfl, p.property,
        childTuple_member _ _ k.val _ (fun i => termCode_member π (children i))⟩
  | neg body =>
      apply left_member
      apply left_member
      apply right_member
      exact formulaCode_member body
  | imp left right =>
      apply left_member
      apply right_member
      simp only [SyntaxPolynomial.power]
      rw [rawCarrier_product_eval]
      exact ⟨formulaCode left, formulaCode right, rfl,
        formulaCode_member left, formulaCode_member right⟩
  | all x body =>
      apply right_member
      rw [rawCarrier_product_eval]
      exact ⟨x, formulaCode body, rfl, by simp [rawCarrier, variableCarrier], formulaCode_member body⟩

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
