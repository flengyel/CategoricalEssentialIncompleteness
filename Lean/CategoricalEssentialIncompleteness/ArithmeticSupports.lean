/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticSyntax
public import CategoricalEssentialIncompleteness.ArithmeticRepresentation
public import CategoricalEssentialIncompleteness.NumericalPredicates

/-!
# Theorem and refutation predicates

The sentence enumeration identifies the provable and refutable sentences of
an arithmetic theory with subsets of the natural numbers. Their support
inclusions are predicates in the full PER subobject lattice. Consistency is
equivalent to disjointness of these two supports.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

/-- Indices of sentences provable in the given theory. -/
def theoremSupport (T : ArithmeticTheory) : Set ℕ :=
  {b | T ⊢ sentenceEnumeration b}

/-- Indices of sentences whose negations are provable in the given theory. -/
def refutationSupport (T : ArithmeticTheory) : Set ℕ :=
  {b | T ⊢ ∼(sentenceEnumeration b)}

@[simp] theorem sentenceIndex_mem_theoremSupport (T : ArithmeticTheory)
    (φ : ArithmeticSentence) : sentenceIndex φ ∈ theoremSupport T ↔ T ⊢ φ := by
  simp only [theoremSupport, Set.mem_ofPred_eq, sentenceEnumeration_index]

@[simp] theorem sentenceIndex_mem_refutationSupport (T : ArithmeticTheory)
    (φ : ArithmeticSentence) : sentenceIndex φ ∈ refutationSupport T ↔ T ⊢ ∼φ := by
  simp only [refutationSupport, Set.mem_ofPred_eq, sentenceEnumeration_index]

theorem supports_disjoint (T : ArithmeticTheory) [Entailment.Consistent T] :
    Disjoint (theoremSupport T) (refutationSupport T) := by
  apply Set.disjoint_left.mpr
  intro n hn hm
  exact ArithmeticRepresentation.consistent_not_both T (sentenceEnumeration n) ⟨hn, hm⟩

/-- Disjointness of theorem and refutation indices is exactly consistency. -/
theorem supports_disjoint_iff (T : ArithmeticTheory) :
    Disjoint (theoremSupport T) (refutationSupport T) ↔ Entailment.Consistent T := by
  constructor
  · intro h
    refine ⟨fun hInc => ?_⟩
    have hp : (0 : ℕ) ∈ theoremSupport T := hInc (sentenceEnumeration 0)
    have hn : (0 : ℕ) ∈ refutationSupport T := hInc (∼(sentenceEnumeration 0))
    exact Set.disjoint_left.mp h hp hn
  · intro h
    let := h
    exact supports_disjoint T

/-- Extending a theory increases its theorem support. -/
theorem theoremSupport_mono {T T' : ArithmeticTheory} (h : T ⪯ T') :
    theoremSupport T ⊆ theoremSupport T' := fun _ hn => h.wk hn

/-- Extending a theory increases its refutation support. -/
theorem refutationSupport_mono {T T' : ArithmeticTheory} (h : T ⪯ T') :
    refutationSupport T ⊆ refutationSupport T' := fun _ hn => h.wk hn

/-- The provability predicate as a PER support subobject. -/
def theoremPredicate (T : ArithmeticTheory) :
    Numerical.predicates.obj (Numerical.totalObject Numerical.nat) :=
  NumericalPER.supportSubobject (theoremSupport T) (Set.subset_univ _)

/-- The refutability predicate as a PER support subobject. -/
def refutationPredicate (T : ArithmeticTheory) :
    Numerical.predicates.obj (Numerical.totalObject Numerical.nat) :=
  NumericalPER.supportSubobject (refutationSupport T) (Set.subset_univ _)

theorem predicates_disjoint (T : ArithmeticTheory) [Entailment.Consistent T] :
    Disjoint (theoremPredicate T) (refutationPredicate T) := by
  apply disjoint_iff.mpr
  change NumericalPER.supportSubobject (theoremSupport T) _ ⊓
    NumericalPER.supportSubobject (refutationSupport T) _ = ⊥
  rw [← NumericalPER.supportSubobject_inf]
  have h := Set.disjoint_iff_inter_eq_empty.mp (supports_disjoint T)
  simp only [h, NumericalPER.supportSubobject_bot]

theorem theoremPredicate_mono {T T' : ArithmeticTheory} (h : T ⪯ T') :
    theoremPredicate T ≤ theoremPredicate T' :=
  (NumericalPER.supportSubobject_le_iff _ _).mpr (theoremSupport_mono h)

theorem refutationPredicate_mono {T T' : ArithmeticTheory} (h : T ⪯ T') :
    refutationPredicate T ≤ refutationPredicate T' :=
  (NumericalPER.supportSubobject_le_iff _ _).mpr (refutationSupport_mono h)

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
