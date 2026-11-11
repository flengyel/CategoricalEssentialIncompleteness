/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionLists

/-! # Standard named-variable lists and their literal arithmetic codes

These equations compare the external lists with the actual PA-defined
list functions at the standard model. The internal equations are proved
separately in the imported numerical implementation.
-/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
open SyntacticSyntax SyntacticSyntax.NatVectors

@[simp] theorem pack_adjoin (x : ℕ) (xs : List ℕ) :
    pack (x :: xs) = adjoin x (pack xs) := by
  rw [pack_cons, FiniteSigmaOne.canonical_adjoin, nat_pair_eq]

@[simp] theorem append_pack (xs ys : List ℕ) :
    Words.append (pack xs) (pack ys) = pack (xs ++ ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.cons_append, pack_adjoin, pack_adjoin, Words.append_adjoin, ih]

@[simp] theorem len_pack (xs : List ℕ) : len (pack xs) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [pack_adjoin, len_adjoin, ih, List.length_cons]

@[simp] theorem member_pack (x : ℕ) (xs : List ℕ) :
    ConcreteNamedSubstitution.member x (pack xs) = if x ∈ xs then 1 else 0 := by
  classical
  induction xs with
  | nil => simp
  | cons y ys ih =>
      rw [pack_adjoin, ConcreteNamedSubstitution.member_adjoin, ih]
      by_cases he : y = x
      · subst y
        simp
      · simp [he, Ne.symm he]

@[simp] theorem member_pack_eq_one (x : ℕ) (xs : List ℕ) :
    ConcreteNamedSubstitution.member x (pack xs) = 1 ↔ x ∈ xs := by
  classical
  rw [member_pack]
  split_ifs <;> simp_all

@[simp] theorem member_pack_eq_zero (x : ℕ) (xs : List ℕ) :
    ConcreteNamedSubstitution.member x (pack xs) = 0 ↔ x ∉ xs := by
  classical
  rw [member_pack]
  split_ifs <;> simp_all

@[simp] theorem delete_pack (x : ℕ) (xs : List ℕ) :
    ConcreteNamedSubstitution.delete x (pack xs) =
      pack (xs.filter (fun y => decide (y ≠ x))) := by
  classical
  induction xs with
  | nil => simp
  | cons y ys ih =>
      by_cases he : y = x
      · have hf : (y :: ys).filter (fun z => decide (z ≠ x)) =
            ys.filter (fun z => decide (z ≠ x)) := by simp [he]
        rw [hf, pack_adjoin, ConcreteNamedSubstitution.delete_adjoin, ite_eq_left he, ih]
      · have hf : (y :: ys).filter (fun z => decide (z ≠ x)) =
            y :: ys.filter (fun z => decide (z ≠ x)) := by simp [he]
        rw [hf, pack_adjoin, pack_adjoin, ConcreteNamedSubstitution.delete_adjoin, ite_eq_right he, ih]

@[simp] theorem pack_eq_zero (xs : List ℕ) : pack xs = 0 ↔ xs = [] := by
  constructor
  · intro h
    apply pack_injective
    simpa only [pack_nil] using h
  · rintro rfl
    rfl

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
