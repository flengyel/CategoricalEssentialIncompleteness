/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalUnions

/-!
# Numerical domain separators and recursive inseparability

The separator inequalities use PER subobjects and complementary
restriction idempotents of the numerical category. They are equivalent to the
existence of a recursive separating set, for arbitrary distinguished supports.
This is the support comparison in part (ii) of the manuscript's numerical
essential-equivalence theorem.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace Numerical

def RecursivelyInseparable (A B : Set ℕ) : Prop :=
  Disjoint A B ∧ ¬ ∃ D : Set ℕ, ComputablePred (· ∈ D) ∧ A ⊆ D ∧ Disjoint D B

/-- Complementarity fixes the second support as the ordinary set complement. -/
theorem complementary_support_compl (a : ComplementaryPair (Domain nat)) :
    a.neg.support = a.pos.supportᶜ := by
  have hi : a.pos.support ∩ a.neg.support = ∅ := by
    rw [← Domain.support_inf, a.compl.inf_eq_bot, Domain.support_bot]
  have hu : a.pos.support ∪ a.neg.support = Set.univ := by
    rw [← Domain.support_sup, a.compl.sup_eq_top, Domain.support_top]; rfl
  ext n
  constructor
  · intro hn hp
    have : n ∈ a.pos.support ∩ a.neg.support := ⟨hp, hn⟩
    rw [hi] at this; exact this
  · intro hn
    have : n ∈ a.pos.support ∪ a.neg.support := by rw [hu]; trivial
    exact this.resolve_left hn

/-- A separator expressed in categorical subobject order. -/
def SeparatesSupports (A B : Set ℕ) (a : ComplementaryPair (Domain nat)) : Prop :=
  NumericalPER.supportSubobject A (Set.subset_univ A) ≤ domainSubobject nat a.pos ∧
  NumericalPER.supportSubobject B (Set.subset_univ B) ≤ domainSubobject nat a.neg

set_option backward.isDefEq.respectTransparency false in
theorem separatesSupports_iff (A B : Set ℕ) (a : ComplementaryPair (Domain nat)) :
    SeparatesSupports A B a ↔ A ⊆ a.pos.support ∧ Disjoint a.pos.support B := by
  change
    (NumericalPER.supportSubobject A _ ≤ NumericalPER.supportSubobject a.pos.support _ ∧
     NumericalPER.supportSubobject B _ ≤ NumericalPER.supportSubobject a.neg.support _) ↔ _
  rw [NumericalPER.supportSubobject_le_iff, NumericalPER.supportSubobject_le_iff,
    complementary_support_compl]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨ha, Set.disjoint_left.mpr (fun n hd hn ↦ hb hn hd)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha, fun n hn hd ↦ Set.disjoint_left.mp hb hd hn⟩

/-- Categorical domain separators are precisely recursive separators of supports. -/
theorem exists_separator_iff (A B : Set ℕ) :
    (∃ a : ComplementaryPair (Domain nat), SeparatesSupports A B a) ↔
      ∃ D : Set ℕ, ComputablePred (· ∈ D) ∧ A ⊆ D ∧ Disjoint D B := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hp, hn⟩ := (separatesSupports_iff A B a).mp ha
    exact ⟨a.pos.support, complementary_support_recursive a, hp, hn⟩
  · rintro ⟨D, hD, hA, hB⟩
    refine ⟨recursivePair D hD, (separatesSupports_iff A B _).mpr ?_⟩
    rw [recursivePair_support]
    exact ⟨hA, hB⟩

/-- Part (ii) of the numerical essential-equivalence theorem. -/
theorem no_separator_iff_recursively_inseparable (A B : Set ℕ) (hAB : Disjoint A B) :
    (¬ ∃ a : ComplementaryPair (Domain nat), SeparatesSupports A B a) ↔
      RecursivelyInseparable A B := by
  constructor
  · intro h
    exact ⟨hAB, (not_congr (exists_separator_iff A B)).mp h⟩
  · intro h
    exact (not_congr (exists_separator_iff A B)).mpr h.2

end Numerical
end CategoricalEssentialIncompleteness
