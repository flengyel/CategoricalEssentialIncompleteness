/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticNumericalSubstitution
public import CategoricalEssentialIncompleteness.ArithmeticSupports
public import CategoricalEssentialIncompleteness.NumericalInseparability

/-!
# Arithmetic representation by substitution

The two representation equations are equalities of PER subobjects.
Pullback of support inclusions identifies these equations with positive and
negative provability of each numeral instance. For a consistent arithmetic
theory, existence of a representing total numerical arrow is equivalent to
strong numeralwise definability. Extensions of `PA⁻` represent every
complementary pair of numerical restriction domains.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits Encodable
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

private theorem numerical_snd_val (z : ℕ) :
    (Numerical.snd (Numerical.totalObject Numerical.nat)
      (Numerical.totalObject Numerical.nat)).hom.val z = Part.some (Nat.unpair z).2 := by
  change (supportIdentity (Numerical.product Numerical.nat Numerical.nat).carrier z).bind
    (fun k => Part.some (Nat.unpair k).2) = _
  have hz : z ∈ (Numerical.product Numerical.nat Numerical.nat).carrier :=
    ⟨Set.mem_univ _, Set.mem_univ _⟩
  rw [supportIdentity, Part.assert_pos hz, Part.bind_some]

private theorem inverseSupport_substitutionRow
    (g : Numerical.totalObject Numerical.nat ⟶ Numerical.totalObject Numerical.nat)
    (A : Set ℕ) :
    NumericalPER.inverseSupport (Numerical.totalRepresentative (substitutionRow g)) A =
      {z | substitutionFunction (Numerical.natFunction g (Nat.unpair z).1)
        (Nat.unpair z).2 ∈ A} := by
  ext z
  change (z ∈ (Numerical.product Numerical.nat Numerical.nat).carrier ∧
    ∃ m ∈ (substitutionRow g).hom.val z, m ∈ A) ↔ _
  rw [substitutionRow_val]
  simp only [Numerical.product, Numerical.nat, Set.mem_ofPred_eq, Set.mem_univ,
    and_self, true_and, Part.mem_some_iff, exists_eq_left]

private theorem inverseSupport_snd (A : Set ℕ) :
    NumericalPER.inverseSupport (Numerical.totalRepresentative
      (Numerical.snd (Numerical.totalObject Numerical.nat)
        (Numerical.totalObject Numerical.nat))) A =
      {z | (Nat.unpair z).2 ∈ A} := by
  ext z
  change (z ∈ (Numerical.product Numerical.nat Numerical.nat).carrier ∧
    ∃ m ∈ (Numerical.snd (Numerical.totalObject Numerical.nat)
      (Numerical.totalObject Numerical.nat)).hom.val z, m ∈ A) ↔ _
  rw [numerical_snd_val]
  simp only [Numerical.product, Numerical.nat, Set.mem_ofPred_eq, Set.mem_univ,
    and_self, true_and, Part.mem_some_iff, exists_eq_left]

/-- Equality of the two pullback subobjects is equality of their
numerical inverse-image supports. -/
theorem pull_support_eq_snd_iff
    (g : Numerical.totalObject Numerical.nat ⟶ Numerical.totalObject Numerical.nat)
    (A B : Set ℕ) :
    Numerical.predicates.pull (substitutionRow g)
        (NumericalPER.supportSubobject A (Set.subset_univ _)) =
      Numerical.predicates.pull
        (Numerical.snd (Numerical.totalObject Numerical.nat)
          (Numerical.totalObject Numerical.nat))
        (NumericalPER.supportSubobject B (Set.subset_univ _)) ↔
      ∀ x n, substitutionFunction (Numerical.natFunction g x) n ∈ A ↔ n ∈ B := by
  change (Subobject.pullback (NumericalPER.ofRepresentative
      (Numerical.totalRepresentative (substitutionRow g)))).obj
        (NumericalPER.supportSubobject A _) =
    (Subobject.pullback (NumericalPER.ofRepresentative (Numerical.totalRepresentative
      (Numerical.snd (Numerical.totalObject Numerical.nat)
        (Numerical.totalObject Numerical.nat))))).obj
        (NumericalPER.supportSubobject B _) ↔ _
  rw [NumericalPER.supportSubobject_pullback, NumericalPER.supportSubobject_pullback,
    NumericalPER.supportSubobject_eq_iff, inverseSupport_substitutionRow, inverseSupport_snd]
  constructor
  · intro h x n
    simpa only [Set.mem_ofPred_eq, Nat.unpair_pair] using Set.ext_iff.mp h (Nat.pair x n)
  · intro h
    ext z
    exact h (Nat.unpair z).1 (Nat.unpair z).2

/-- The positive and negative representation equations for arithmetic substitution. -/
def RepresentsPair (T : ArithmeticTheory)
    (a : ComplementaryPair (Numerical.Domain Numerical.nat))
    (g : Numerical.totalObject Numerical.nat ⟶ Numerical.totalObject Numerical.nat) : Prop :=
  Numerical.predicates.pull (substitutionRow g) (theoremPredicate T) =
      Numerical.predicates.pull
        (Numerical.snd (Numerical.totalObject Numerical.nat)
          (Numerical.totalObject Numerical.nat)) (Numerical.domainSubobject Numerical.nat a.pos) ∧
  Numerical.predicates.pull (substitutionRow g) (refutationPredicate T) =
      Numerical.predicates.pull
        (Numerical.snd (Numerical.totalObject Numerical.nat)
          (Numerical.totalObject Numerical.nat)) (Numerical.domainSubobject Numerical.nat a.neg)

/-- Representation equations express provability and refutability of each
individual numeral instance, at every value of the parameter. -/
theorem representsPair_iff (T : ArithmeticTheory)
    (a : ComplementaryPair (Numerical.Domain Numerical.nat))
    (g : Numerical.totalObject Numerical.nat ⟶ Numerical.totalObject Numerical.nat) :
    RepresentsPair T a g ↔ ∀ x n : ℕ,
      (T ⊢ ((unaryFormula (Numerical.natFunction g x))/[
        (↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔ n ∈ a.pos.support) ∧
      (T ⊢ ∼((unaryFormula (Numerical.natFunction g x))/[
        (↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔ n ∈ a.neg.support) := by
  change
    (Numerical.predicates.pull (substitutionRow g)
        (NumericalPER.supportSubobject (theoremSupport T) _) =
      Numerical.predicates.pull
        (Numerical.snd (Numerical.totalObject Numerical.nat)
          (Numerical.totalObject Numerical.nat))
        (NumericalPER.supportSubobject a.pos.support _) ∧
    Numerical.predicates.pull (substitutionRow g)
        (NumericalPER.supportSubobject (refutationSupport T) _) =
      Numerical.predicates.pull
        (Numerical.snd (Numerical.totalObject Numerical.nat)
          (Numerical.totalObject Numerical.nat))
        (NumericalPER.supportSubobject a.neg.support _)) ↔ _
  rw [pull_support_eq_snd_iff, pull_support_eq_snd_iff]
  simp only [theoremSupport, refutationSupport, Set.mem_ofPred_eq,
    sentenceEnumeration_substitutionFunction]
  exact ⟨fun h x n => ⟨h.1 x n, h.2 x n⟩,
    fun h => ⟨fun x n => (h x n).1, fun x n => (h x n).2⟩⟩

/-- A strong numeralwise definition gives a constant representing parameter arrow. -/
theorem representsPair_constant (T : ArithmeticTheory) [Entailment.Consistent T]
    (a : ComplementaryPair (Numerical.Domain Numerical.nat))
    (φ : ArithmeticSemisentence 1)
    (hφ : ArithmeticRepresentation.StrongNumeralwise T (· ∈ a.pos.support) φ) :
    RepresentsPair T a (Numerical.natArrow (fun _ => encode φ) (Computable.const _)) := by
  apply (representsPair_iff T a _).mpr
  intro x n
  simp only [Numerical.natFunction_natArrow, unaryFormula_encode]
  rw [Numerical.complementary_support_compl]
  exact ⟨hφ.provable_iff n, hφ.provable_neg_iff n⟩

/-- A complementary pair has a representing parameter arrow exactly when its
positive support has a strong numeralwise definition. -/
theorem exists_representsPair_iff_strongNumeralwise (T : ArithmeticTheory)
    [Entailment.Consistent T] (a : ComplementaryPair (Numerical.Domain Numerical.nat)) :
    (∃ g, RepresentsPair T a g) ↔
      ∃ φ : ArithmeticSemisentence 1,
        ArithmeticRepresentation.StrongNumeralwise T (· ∈ a.pos.support) φ := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨unaryFormula (Numerical.natFunction g 0), ?_⟩
    intro n
    have h := (representsPair_iff T a g).mp hg 0 n
    rw [Numerical.complementary_support_compl] at h
    exact ⟨h.1.mpr, h.2.mpr⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨_, representsPair_constant T a φ hφ⟩

/-- The representation equivalence stated for a recursive subset of natural numbers. -/
theorem recursiveSet_adequacy_iff (T : ArithmeticTheory) [Entailment.Consistent T]
    (A : Set ℕ) (hA : ComputablePred (· ∈ A)) :
    (∃ g, RepresentsPair T (Numerical.recursivePair A hA) g) ↔
      ∃ φ : ArithmeticSemisentence 1,
        ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ := by
  rw [exists_representsPair_iff_strongNumeralwise, Numerical.recursivePair_support]

/-- Representation of all complementary pairs is exactly strong numeralwise
definability of every recursive set. -/
theorem represents_all_pairs_iff (T : ArithmeticTheory) [Entailment.Consistent T] :
    (∀ a : ComplementaryPair (Numerical.Domain Numerical.nat), ∃ g, RepresentsPair T a g) ↔
      ∀ A : Set ℕ, ComputablePred (· ∈ A) →
        ∃ φ : ArithmeticSemisentence 1,
          ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ := by
  constructor
  · intro h A hA
    exact (recursiveSet_adequacy_iff T A hA).mp (h (Numerical.recursivePair A hA))
  · intro h a
    exact (exists_representsPair_iff_strongNumeralwise T a).mpr
      (h a.pos.support (Numerical.complementary_support_recursive a))

/-- Every complemented numerical restriction domain is represented over a
consistent extension of `PA⁻`, without a computable-enumerability premise on the theory. -/
theorem every_pair_represented (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] (a : ComplementaryPair (Numerical.Domain Numerical.nat)) :
    ∃ g, RepresentsPair T a g := by
  apply (exists_representsPair_iff_strongNumeralwise T a).mpr
  exact ⟨_, ArithmeticRepresentation.codeOfComputablePred_strongNumeralwise T
    (Numerical.complementary_support_recursive a)⟩

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
