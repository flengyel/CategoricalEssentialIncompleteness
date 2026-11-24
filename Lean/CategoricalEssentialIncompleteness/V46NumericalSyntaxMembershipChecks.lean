/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalSyntaxMembership

/-! # The two recursive word predicates in Proposition 8.8 -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxMembershipChecks

/-- Extend the finite family by empty symbol objects beyond the arity bound. -/
private def symbols {d : ℕ} (S : Fin (d + 1) → Set ℕ)
    (hS : ∀ k, ComputablePred (· ∈ S k)) (k : ℕ) : EnumerableCarriers.Total :=
  if h : k < d + 1 then ⟨⟨S ⟨k, h⟩, (hS ⟨k, h⟩).to_re⟩⟩
  else ⟨⟨∅, REPred.const False⟩⟩

private theorem recursive_support {d : ℕ} (S : Fin (d + 1) → Set ℕ)
    (hS : ∀ k, ComputablePred (· ∈ S k)) (k : ℕ) (hk : k ≤ d) :
    ComputablePred (· ∈ (symbols S hS k).obj.support) := by
  simpa only [symbols, dite_eq_left (Nat.lt_succ_of_le hk)] using hS ⟨k, Nat.lt_succ_of_le hk⟩

/-- Each fixed finite signature supplies a decision program for terms and a decision
program for formulas. Both programs accept arbitrary natural-number inputs. -/
example (d : ℕ) (σ₀ π₀ : Fin (d + 1) → Set ℕ)
    (hσ : ∀ k, ComputablePred (· ∈ σ₀ k)) (hπ : ∀ k, ComputablePred (· ∈ π₀ k)) :
    let V := NumericalCoordinates.codedPredicate NumericalNamed.variableObject
    let a := SyntaxPolynomial.termExpression V
      (fun k => NumericalCoordinates.codedPredicate (NumericalTuples.unary (symbols σ₀ hσ k))) d
    let b := SyntaxPolynomial.formulaExpression V
      (fun k => NumericalCoordinates.codedPredicate (NumericalTuples.unary (symbols π₀ hπ k))) d
    ∃ term formula : ℕ → Bool, Computable term ∧ Computable formula ∧
      (∀ w : ℕ, term w = true ↔ (SyntacticSyntax.Postfix.plainCarrier false a b).val.Evalb ![w]) ∧
      (∀ w : ℕ, formula w = true ↔
        (SyntacticSyntax.Postfix.plainCarrier true a b).val.Evalb ![w]) := by
  dsimp only
  have h := NumericalSyntaxMembership.numerical_word_membership
    (symbols σ₀ hσ) (symbols π₀ hπ) d (recursive_support σ₀ hσ) (recursive_support π₀ hπ)
  obtain ⟨t, ht, et⟩ := ComputablePred.computable_iff.mp (h false)
  obtain ⟨f, hf, ef⟩ := ComputablePred.computable_iff.mp (h true)
  exact ⟨t, f, ht, hf, fun w => (iff_of_eq (congrFun et w)).symm,
    fun w => (iff_of_eq (congrFun ef w)).symm⟩

#print axioms NumericalSyntaxMembership.postfix_membership
#print axioms NumericalSyntaxMembership.numerical_word_membership

end CategoricalEssentialIncompleteness.V46.NumericalSyntaxMembershipChecks
