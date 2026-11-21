/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionRoots

/-! # Scalar result equations used to compare the term algebra step -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedComparisonTermRootArithmeticDecidableEq : DecidableEq M := Classical.decEq M

theorem termOnly_power (f g h : M → M) (n : ℕ) (u : M) :
    ConcreteNamedSubstitution.mapChildren f g (SyntaxPolynomial.power .term n) u =
      ConcreteNamedSubstitution.mapChildren f h (SyntaxPolynomial.power .term n) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
        change Arithmetic.pair
          (ConcreteNamedSubstitution.mapChildren f g (SyntaxPolynomial.power .term (n+1)) (π₁ u)) (f (π₂ u)) =
          Arithmetic.pair
          (ConcreteNamedSubstitution.mapChildren f h (SyntaxPolynomial.power .term (n+1)) (π₁ u)) (f (π₂ u))
        rw [ih]

theorem termOnly_constructors (σ : ℕ → Carrier) (f g h : M → M) (n : ℕ) (u : M) :
    ConcreteNamedSubstitution.mapChildren f g (SyntaxPolynomial.constructors σ n) u =
      ConcreteNamedSubstitution.mapChildren f h (SyntaxPolynomial.constructors σ n) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      simp only [SyntaxPolynomial.constructors,ConcreteNamedSubstitution.mapChildren,ih,termOnly_power f g h]

theorem termRoot_variable_result (V : Carrier) (σ : ℕ → Carrier) (d : ℕ)
    (x replacement fv name : M) :
    ConcreteNamedSubstitution.result
      (ConcreteNamedSubstitution.termRoot V σ d (Arithmetic.pair x (Arithmetic.pair replacement fv))
        (Arithmetic.pair name 0)) =
      if name = x then replacement else
        Coding.constructor false (SyntaxPolynomial.termExpression V σ d) (Arithmetic.pair name 0) := by
  simp [ConcreteNamedSubstitution.termRoot,ConcreteNamedSubstitution.mapChildren,SyntaxPolynomial.termExpression]

theorem termRoot_function_result (V : Carrier) (σ : ℕ → Carrier) (d : ℕ)
    (x replacement fv u : M) :
    ConcreteNamedSubstitution.result
      (ConcreteNamedSubstitution.termRoot V σ d (Arithmetic.pair x (Arithmetic.pair replacement fv))
        (Arithmetic.pair u 1)) =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d)
        (Arithmetic.pair (ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
          ConcreteNamedSubstitution.original (SyntaxPolynomial.constructors σ d) u) 1) := by
  simp only [ConcreteNamedSubstitution.termRoot,ConcreteNamedSubstitution.result_payload,
    pi₂_pair,_root_.one_ne_zero,↓reduceIte,SyntaxPolynomial.termExpression,ConcreteNamedSubstitution.mapChildren,
    pi₁_pair]
  rw [termOnly_constructors σ ConcreteNamedSubstitution.result ConcreteNamedSubstitution.successfulValue
    ConcreteNamedSubstitution.original d u]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
