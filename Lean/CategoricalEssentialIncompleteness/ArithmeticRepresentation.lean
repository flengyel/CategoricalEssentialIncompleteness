/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Numeralwise representation of computable predicates

A representing formula proves each true numerical instance and refutes each
false numerical instance. Consistency makes these implications equivalences,
and representation persists under extension of the theory.
-/

set_option autoImplicit false
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness
namespace ArithmeticRepresentation

/-- Positive and negative provability for each individual numerical instance. -/
def StrongNumeralwise (T : ArithmeticTheory) (p : ℕ → Prop)
    (φ : ArithmeticSemisentence 1) : Prop :=
  ∀ n : ℕ,
    (p n → T ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) ∧
    (¬p n → T ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence))

/-- A consistent arithmetic theory cannot prove a sentence and its negation. -/
theorem consistent_not_both (T : ArithmeticTheory) [Entailment.Consistent T]
    (φ : ArithmeticSentence) : ¬(T ⊢ φ ∧ T ⊢ ∼φ) := by
  rintro ⟨hφ, hnφ⟩
  exact Entailment.Consistent.not_inc (𝓢 := T) inferInstance
    (Entailment.inconsistent_of_provable_of_unprovable hφ hnφ)

namespace StrongNumeralwise

variable {T T' : ArithmeticTheory} {p : ℕ → Prop} {φ : ArithmeticSemisentence 1}

/-- In a consistent theory, the represented predicate is exactly the set of
provable numeral instances. -/
theorem provable_iff [Entailment.Consistent T] (h : StrongNumeralwise T p φ) (n : ℕ) :
    T ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔ p n := by
  constructor
  · intro hφ
    by_contra hp
    exact consistent_not_both T _ ⟨hφ, (h n).2 hp⟩
  · exact (h n).1

/-- In a consistent theory, refutable numeral instances represent the
complement of the predicate. -/
theorem provable_neg_iff [Entailment.Consistent T] (h : StrongNumeralwise T p φ) (n : ℕ) :
    T ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔ ¬p n := by
  constructor
  · intro hnφ hp
    exact consistent_not_both T _ ⟨(h n).1 hp, hnφ⟩
  · exact (h n).2

/-- Every extension of the theory retains its numeralwise representation. -/
theorem mono (h : StrongNumeralwise T p φ) (hTT' : T ⪯ T') :
    StrongNumeralwise T' p φ := by
  intro n
  exact ⟨fun hn ↦ hTT'.wk ((h n).1 hn), fun hn ↦ hTT'.wk ((h n).2 hn)⟩

end StrongNumeralwise

/-- The formula `codeOfComputablePred` strongly represents every computable
predicate in each extension of `PA⁻`. -/
theorem codeOfComputablePred_strongNumeralwise (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    {p : ℕ → Prop} (hp : ComputablePred p) :
    StrongNumeralwise T p (codeOfComputablePred p) := by
  let : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  intro n
  exact ⟨codeOfComputablePred_provable hp, codeOfComputablePred_provable_neg hp⟩

/-- A computable predicate has a numeralwise representing formula whose
positive and negative instances are exact in every consistent extension of `T`. -/
theorem computable_has_persistent_representation (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    {p : ℕ → Prop} (hp : ComputablePred p) :
    ∃ φ : ArithmeticSemisentence 1, StrongNumeralwise T p φ ∧
      ∀ (T' : ArithmeticTheory), T ⪯ T' → Entailment.Consistent T' →
        ∀ n : ℕ,
          (T' ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔ p n) ∧
          (T' ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔ ¬p n) := by
  refine ⟨codeOfComputablePred p, codeOfComputablePred_strongNumeralwise T hp, ?_⟩
  intro T' hTT' hT' n
  let := hT'
  have h := (codeOfComputablePred_strongNumeralwise T hp).mono hTT'
  exact ⟨h.provable_iff n, h.provable_neg_iff n⟩

end ArithmeticRepresentation
end CategoricalEssentialIncompleteness
