/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixComparison
public import CategoricalEssentialIncompleteness.V46NamedStandardLists
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionMap
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionGather

/-! # Standard polynomial operations on ordered named payloads -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
open ConcreteNamedSubstitution

@[simp] theorem mapChildren_childTuple (f g : ℕ → ℕ) (n : ℕ) (c : Fin n → ℕ) :
    mapChildren f g (SyntaxPolynomial.power .term n) (childTuple n c) =
      childTuple n (fun i => f (c i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n => simp [SyntaxPolynomial.power, childTuple, mapChildren, ih]

@[simp] theorem mapChildren_arityInput (σ : ℕ → Carrier) (f g : ℕ → ℕ)
    (d : ℕ) (k : Fin (d + 1)) (s : ℕ) (c : Fin k.val → ℕ) :
    mapChildren f g (SyntaxPolynomial.constructors σ d)
      (arityInput d k (Arithmetic.pair s (childTuple k.val c))) =
    arityInput d k (Arithmetic.pair s (childTuple k.val (fun i => f (c i)))) := by
  induction d with
  | zero =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      simp [SyntaxPolynomial.constructors, arityInput, mapChildren]
  | succ d ih =>
      revert c
      refine Fin.lastCases ?_ (fun k => ?_) k
      · intro c
        simp [SyntaxPolynomial.constructors, arityInput, Fin.lastCases_last, mapChildren]
      · intro c
        simp [SyntaxPolynomial.constructors, arityInput, Fin.lastCases_castSucc, mapChildren, ih]

@[simp] theorem gather_childTuple (n : ℕ) (c : Fin n → List ℕ) :
    gather (SyntaxPolynomial.power .term n) (childTuple n (fun i => pack (c i))) =
      pack (List.ofFn c).flatten := by
  induction n with
  | zero => simp [SyntaxPolynomial.power, childTuple, gather]
  | succ n ih =>
      cases n with
      | zero => simp [SyntaxPolynomial.power, childTuple, gather, List.ofFn_succ]
      | succ n =>
          simp only [SyntaxPolynomial.power, childTuple, gather, pi₁_pair, pi₂_pair]
          rw [ih, append_pack]
          congr 1
          rw [List.ofFn_succ' c, List.concat_eq_append, List.flatten_append]
          simp

@[simp] theorem gather_arityInput (σ : ℕ → Carrier) (d : ℕ)
    (k : Fin (d + 1)) (s : ℕ) (c : Fin k.val → List ℕ) :
    gather (SyntaxPolynomial.constructors σ d)
      (arityInput d k (Arithmetic.pair s (childTuple k.val (fun i => pack (c i))))) =
      pack (List.ofFn c).flatten := by
  induction d with
  | zero =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      simp [SyntaxPolynomial.constructors, arityInput, gather]
  | succ d ih =>
      revert c
      refine Fin.lastCases ?_ (fun k => ?_) k
      · intro c
        simp [SyntaxPolynomial.constructors, arityInput, Fin.lastCases_last, gather]
      · intro c
        simp [SyntaxPolynomial.constructors, arityInput, Fin.lastCases_castSucc, gather, ih]

/-- Numerical option tags used by the concrete traversal. -/
def optionCode {σ π : ℕ → Carrier} {d : ℕ} :
    Option (NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) → ℕ
  | none => 0
  | some φ => Arithmetic.pair (formulaCode φ) 1

@[simp] theorem optionCode_none {σ π : ℕ → Carrier} {d : ℕ} :
    optionCode (none : Option (NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)) = 0 := rfl

@[simp] theorem optionCode_some {σ π : ℕ → Carrier} {d : ℕ}
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    optionCode (some φ) = Arithmetic.pair (formulaCode φ) 1 := rfl

@[simp] theorem optionCode_tag {σ π : ℕ → Carrier} {d : ℕ}
    (o : Option (NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)) :
    π₂ (optionCode o) = if o.isSome then 1 else 0 := by
  have hz : (pi₂ (0 : ℕ)) = 0 := by rw [nat_pi₂_eq]; rfl
  cases o <;> simp [optionCode, hz]

theorem optionCode_injective {σ π : ℕ → Carrier} {d : ℕ} :
    Function.Injective (optionCode (σ := σ) (π := π) (d := d)) := by
  intro a b h
  have hz : (pi₂ (0 : ℕ)) = 0 := by rw [nat_pi₂_eq]; rfl
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some φ =>
          have ht := congrArg (pi₂ : ℕ → ℕ) h
          simp [optionCode, hz] at ht
  | some φ =>
      cases b with
      | none =>
          have ht := congrArg (pi₂ : ℕ → ℕ) h
          simp [optionCode, hz] at ht
      | some ψ =>
          have he : formulaCode φ = formulaCode ψ :=
            ((pair_eq_pair_iff _ _ _ _).mp h).1
          exact congrArg some (formulaCode_injective he)

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
