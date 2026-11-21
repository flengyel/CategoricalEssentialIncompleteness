/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticDomainApplication
public import CategoricalEssentialIncompleteness.NumericalInseparability

/-! # Recursive inseparability and incompleteness from the categorical application -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication

open ClassicalPrograms PartialFunctions

theorem sentence_top_support : splitSupport (⊤ : Idem sentenceObject) = sentenceSet := by
  change support (inclusionRangeFunctor.mapIdem (supportIdem sentenceSet sentenceSet_re)) = sentenceSet
  rw [supportIdem_image, support_setIdem]

def separatorIdem (D : Set ℕ) (hD : ComputablePred (· ∈ D)) : Idem sentenceObject :=
  SplitObject.relativeIdem (supportIdem (D ∩ sentenceSet) (re_inter hD.to_re sentenceSet_re))
    (supportIdem_le (re_inter hD.to_re sentenceSet_re) sentenceSet_re Set.inter_subset_right)

theorem separator_support (D : Set ℕ) (hD : ComputablePred (· ∈ D)) :
    splitSupport (separatorIdem D hD) = D ∩ sentenceSet :=
  splitSupport_relative (re_inter hD.to_re sentenceSet_re) sentenceSet_re Set.inter_subset_right

theorem separators_complementary (D : Set ℕ) (hD : ComputablePred (· ∈ D)) :
    Complementary (separatorIdem D hD) (separatorIdem Dᶜ hD.not) := by
  constructor
  · apply splitSupport_injective
    rw [splitSupport_inf, separator_support, separator_support, splitSupport_bot]
    ext n
    simp
    tauto
  · apply splitSupport_injective
    rw [splitSupport_sup, separator_support, separator_support, sentence_top_support]
    ext n
    classical
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto

/-- No recursive predicate on sentence codes separates the theorems from the refutable
sentences. -/
theorem theorem_refutation_recursivelyInseparable (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] [T.RE] (hT : Consistent T) :
    Numerical.RecursivelyInseparable (theoremCodes T) (refutationCodes T) := by
  have hi := (categorical_arithmetic T hT).1
  constructor
  · have he := congrArg splitSupport hi.disjoint
    rw [splitSupport_inf, theoremIdem_support, refutationIdem_support, splitSupport_bot] at he
    exact Set.disjoint_iff_inter_eq_empty.mpr he
  · rintro ⟨D, hD, hth, href⟩
    apply hi.no_separator
    refine ⟨separatorIdem D hD, separatorIdem Dᶜ hD.not, separators_complementary D hD, ?_, ?_⟩
    · rw [splitSupport_le_iff, theoremIdem_support, separator_support]
      exact fun n hn => ⟨hth hn, theoremCodes_subset T hn⟩
    · rw [splitSupport_le_iff, refutationIdem_support, separator_support]
      intro n hn
      exact ⟨fun hd => Set.disjoint_left.mp href hd hn, hn.1⟩

theorem completeness_covers_domains (T : ArithmeticTheory) [T.RE] [Complete T] :
    theoremIdem T ⊔ Idem.pull negation (theoremIdem T) = ⊤ := by
  apply splitSupport_injective
  rw [splitSupport_sup, theoremIdem_support, refutationIdem_support, sentence_top_support]
  ext n
  constructor
  · rintro (hn | hn)
    · exact theoremCodes_subset T hn
    · exact hn.1
  · rintro ⟨φ, rfl⟩
    rcases Complete.con (𝓢 := T) φ with hp | hn
    · exact Or.inl ⟨φ, rfl, hp⟩
    · refine Or.inr ⟨⟨φ, rfl⟩, ?_⟩
      rw [negationCode_encode, mem_theoremCodes_encode]
      exact hn

/-- Logical incompleteness is a consequence of the categorical coverage obstruction. -/
theorem arithmetic_incomplete (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [T.RE] (hT : Consistent T) :
    Incomplete T := by
  apply not_complete_iff_incomplete.mp
  intro hc
  letI := hc
  exact (categorical_arithmetic T hT).2 (completeness_covers_domains T)

/-- The Turing diagonal and section lifting give essential incompleteness under the
consistency hypothesis. -/
theorem essential_incompleteness_of_arithmetic (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] [T.RE] (hT : Consistent T) :
    Numerical.RecursivelyInseparable (theoremCodes T) (refutationCodes T) ∧ Incomplete T :=
  ⟨theorem_refutation_recursivelyInseparable T hT, arithmetic_incomplete T hT⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication
