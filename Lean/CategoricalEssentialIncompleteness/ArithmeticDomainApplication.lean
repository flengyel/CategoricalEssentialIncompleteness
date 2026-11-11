/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticProofDomains
public import CategoricalEssentialIncompleteness.ClassicalDiagonalArithmetic
public import CategoricalEssentialIncompleteness.ArithmeticFormulaSubstitution

/-! # The arithmetic application through the new categorical chain -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Encodable CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication

open ClassicalPrograms PartialFunctions

def negationCode : ℕ → ℕ := Bootstrapping.neg ℒₒᵣ

theorem negationCode_computable : Computable negationCode := by
  change Computable (Bootstrapping.neg ℒₒᵣ : ℕ → ℕ)
  exact computable_iff_sigma1.mpr inferInstance

@[simp] theorem negationCode_encode (φ : ArithmeticSentence) :
    negationCode (encode φ) = encode (∼φ) := by
  rw [← Sentence.quote_eq_encode_nat, ← Sentence.quote_eq_encode_nat]
  simp [negationCode, Sentence.quote_def, Semiformula.quote_def]

theorem negationCode_closed (n : ℕ) (hn : n ∈ sentenceSet) : negationCode n ∈ sentenceSet := by
  obtain ⟨φ, rfl⟩ := hn
  exact ⟨∼φ, (negationCode_encode φ).symm⟩

def negation : sentenceObject ⟶ sentenceObject :=
  totalArrow sentenceSet_re sentenceSet_re negationCode negationCode_computable negationCode_closed

theorem negation_total : isTotal negation :=
  totalArrow_isTotal sentenceSet_re sentenceSet_re negationCode negationCode_computable negationCode_closed

def thetaSentence (n : ℕ) : ArithmeticSentence :=
  (outputPredicate 0).val/[(↑n : ArithmeticSemiterm Empty 0)]

def thetaCode (n : ℕ) : ℕ := encode (thetaSentence n)

theorem thetaCode_computable : Computable thetaCode :=
  Computable.encode.comp (computable_numeralSubstitution.comp
    (Computable.const (outputPredicate 0).val) Computable.id)

theorem thetaCode_closed (n : ℕ) : thetaCode n ∈ sentenceSet := ⟨thetaSentence n, rfl⟩

def theta : parameterObject ⟶ sentenceObject :=
  totalFromU sentenceSet_re thetaCode thetaCode_computable thetaCode_closed

theorem theta_total : isTotal theta :=
  totalFromU_isTotal sentenceSet_re thetaCode thetaCode_computable thetaCode_closed

@[simp] theorem theoremIdem_support (T : ArithmeticTheory) [T.RE] :
    splitSupport (theoremIdem T) = theoremCodes T :=
  splitSupport_relative (theoremCodes_re T) sentenceSet_re (theoremCodes_subset T)

def refutationCodes (T : ArithmeticTheory) : Set ℕ :=
  {n | n ∈ sentenceSet ∧ negationCode n ∈ theoremCodes T}

theorem refutationIdem_support (T : ArithmeticTheory) [T.RE] :
    splitSupport (Idem.pull negation (theoremIdem T)) = refutationCodes T := by
  rw [splitSupport_pull, theoremIdem_support]
  ext n
  change (∃ y, y ∈ restrictedFunction sentenceSet negationCode n ∧ y ∈ theoremCodes T) ↔
    n ∈ sentenceSet ∧ negationCode n ∈ theoremCodes T
  constructor
  · rintro ⟨y, hy, ht⟩
    obtain ⟨hn, he⟩ := (mem_restrictedFunction _ _ n y).mp hy
    exact ⟨hn, he ▸ ht⟩
  · rintro ⟨hn, ht⟩
    exact ⟨negationCode n, (mem_restrictedFunction _ _ n _).mpr ⟨hn, rfl⟩, ht⟩

theorem theta_theorem_support (T : ArithmeticTheory) [T.RE] :
    splitSupport (Idem.pull theta (theoremIdem T)) = {n | thetaCode n ∈ theoremCodes T} := by
  rw [splitSupport_pull, theoremIdem_support]
  ext n
  change (∃ y, y ∈ Part.some (thetaCode n) ∧ y ∈ theoremCodes T) ↔ thetaCode n ∈ theoremCodes T
  simp only [Part.mem_some_iff, exists_eq_left]

theorem theta_refutation_support (T : ArithmeticTheory) [T.RE] :
    splitSupport (Idem.pull theta (Idem.pull negation (theoremIdem T))) =
      {n | negationCode (thetaCode n) ∈ theoremCodes T} := by
  rw [splitSupport_pull, refutationIdem_support]
  ext n
  change (∃ y, y ∈ Part.some (thetaCode n) ∧ y ∈ refutationCodes T) ↔ _
  simp only [Part.mem_some_iff, exists_eq_left]
  exact and_iff_right (thetaCode_closed n)

/-- First numeral-substitution inclusion in Section 7. -/
theorem even_le_theorems : SplitObject.includedIdem evenDiagonal ≤ Idem.pull theta (theoremIdem 𝗣𝗔) := by
  apply (splitSupport_le_iff _ _).mpr
  intro n hn
  change n ∈ support (inclusionRangeFunctor.mapIdem evenDiagonal) at hn
  have ha := (evenDiagonal_support n).mp hn
  rw [theta_theorem_support]
  exact (mem_theoremCodes_encode 𝗣𝗔 (thetaSentence n)).mpr (output_numeral_provable 0 n ha)

/-- Second numeral-substitution inclusion, using the odd computation and
PA-provable universal disjointness. -/
theorem odd_le_refutations : SplitObject.includedIdem oddDiagonal ≤
    Idem.pull theta (Idem.pull negation (theoremIdem 𝗣𝗔)) := by
  apply (splitSupport_le_iff _ _).mpr
  intro n hn
  change n ∈ support (inclusionRangeFunctor.mapIdem oddDiagonal) at hn
  have hb := (oddDiagonal_support n).mp hn
  rw [theta_refutation_support]
  change negationCode (encode (thetaSentence n)) ∈ theoremCodes 𝗣𝗔
  rw [negationCode_encode, mem_theoremCodes_encode]
  exact odd_output_refutes_even n hb

theorem theoremIdem_mono {T T' : ArithmeticTheory} [T.RE] [T'.RE] [T ⪯ T'] :
    theoremIdem T ≤ theoremIdem T' := by
  rw [splitSupport_le_iff, theoremIdem_support, theoremIdem_support]
  exact theoremCodes_mono

theorem theorem_refutation_disjoint (T : ArithmeticTheory) [T.RE] (hT : Consistent T) :
    theoremIdem T ⊓ Idem.pull negation (theoremIdem T) = ⊥ := by
  letI := hT
  apply splitSupport_injective
  rw [splitSupport_inf, theoremIdem_support, refutationIdem_support, splitSupport_bot]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro n ⟨⟨φ, hφ, hp⟩, hn⟩
  subst n
  have hneg : T ⊢ ∼φ := (mem_theoremCodes_encode T (∼φ)).mp (by
    rw [← negationCode_encode]
    exact hn.2)
  exact ArithmeticRepresentation.consistent_not_both T φ ⟨hp, hneg⟩

/-- Corollary 6.7 applied to the classical pair constructed by Theorem 6.3,
the actual sentence/proof objects, and the two proved base inclusions. -/
theorem categorical_arithmetic (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [T.RE] (hT : Consistent T) :
    Inseparable (theoremIdem T) (Idem.pull negation (theoremIdem T)) ∧
      theoremIdem T ⊔ Idem.pull negation (theoremIdem T) ≠ ⊤ :=
  domain_incompleteness (SplitObject.inclusion_inseparable diagonal_inseparable)
    theta theta_total negation negation_total (theoremIdem 𝗣𝗔)
    even_le_theorems odd_le_refutations (theoremIdem T) theoremIdem_mono
    (theorem_refutation_disjoint T hT)

end CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication
