/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanTruthTables

/-! # Boolean validity of the seven first-order schemes -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)

@[reassoc] theorem hilbert_one_value :
    S.hilbertOne ≫ valuation S d = Two.constant _ true := by
  simpa only [CategoricalSyntax.hilbertOne, Category.assoc, implication_value,
    Two.comp_binary, prod.lift_fst_assoc, prod.lift_snd_assoc, prod.lift_fst,
    prod.lift_snd] using implication_one
      ((prod.fst : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ _) ≫ valuation S d)
      (prod.snd ≫ valuation S d)

@[reassoc] theorem hilbert_two_value :
    S.hilbertTwo ≫ valuation S d = Two.constant _ true := by
  simp only [CategoricalSyntax.hilbertTwo, Category.assoc, implication_value,
    Two.comp_binary, prod.lift_fst_assoc, prod.lift_snd_assoc]
  exact implication_two _ _ _

@[reassoc] theorem hilbert_three_value :
    S.hilbertThree ≫ valuation S d = Two.constant _ true := by
  simp only [CategoricalSyntax.hilbertThree, Category.assoc, implication_value,
    negation_value, Two.comp_binary, Two.comp_unary,
    prod.lift_fst_assoc, prod.lift_snd_assoc]
  exact implication_three _ _

theorem substitution_input_value {W : D} (i : W ⟶ S.admissibleSubstitution)
    (a : W ⟶ S.algebra.a.2 ⨯ S.substitutionParameters)
    (ha : a = i ≫ S.admissibleInclusion) :
    i ≫ S.formulaSubstitution ≫ valuation S d = a ≫ prod.fst ≫ valuation S d := by
  rw [substitution_value]
  simpa only [Category.assoc] using congrArg (fun h => h ≫ prod.fst ≫ valuation S d) ha.symm

@[reassoc] theorem hilbert_instantiation_value :
    S.hilbertInstantiation ≫ valuation S d = Two.constant _ true := by
  have hs := substitution_input_value S d S.instantiationAdmissible
    (S.instantiationInclusion ≫ S.instantiationInput) S.instantiation_admissible
  simp only [CategoricalSyntax.instantiationInput, Category.assoc,
    prod.lift_fst_assoc] at hs
  simp only [CategoricalSyntax.hilbertInstantiation, Category.assoc, implication_value,
    quantifier_value, Two.comp_binary, prod.lift_fst_assoc, prod.lift_snd_assoc,
    hs]
  exact implication_self _

@[reassoc] theorem hilbert_distribution_value :
    S.hilbertDistribution ≫ valuation S d = Two.constant _ true := by
  simp only [CategoricalSyntax.hilbertDistribution, Category.assoc, implication_value,
    quantifier_value, Two.comp_binary, prod.lift_fst_assoc, prod.lift_snd_assoc]
  exact implication_self _

@[reassoc] theorem hilbert_reflexivity_value :
    S.hilbertReflexivity ≫ valuation S d = Two.constant _ true := by
  simp [CategoricalSyntax.hilbertReflexivity, Category.assoc, equality_value]

@[reassoc] theorem hilbert_equality_value :
    S.hilbertEquality ≫ valuation S d = Two.constant _ true := by
  have h₁ := substitution_input_value S d S.equalityFirstAdmissible
    (S.equalitySchemeInclusion ≫ S.equalityFirstInput) S.equality_first_admissible
  have h₂ := substitution_input_value S d S.equalitySecondAdmissible
    (S.equalitySchemeInclusion ≫ S.equalitySecondInput) S.equality_second_admissible
  simp only [CategoricalSyntax.equalityFirstInput, CategoricalSyntax.equalitySecondInput,
    Category.assoc, prod.lift_fst_assoc] at h₁ h₂
  simp only [CategoricalSyntax.hilbertEquality, Category.assoc, implication_value,
    equality_value, Two.comp_binary, prod.lift_fst_assoc, prod.lift_snd_assoc,
    Two.comp_constant, h₁, h₂, implication_self]

@[reassoc] theorem logical_axioms_value :
    S.logicalAxioms ≫ valuation S d = Two.constant _ true := by
  unfold CategoricalSyntax.logicalAxioms
  dsimp only [CategoricalSyntax.logicalParameters]
  apply coprod.hom_ext
  · apply coprod.hom_ext
    · apply coprod.hom_ext
      · apply coprod.hom_ext
        · apply coprod.hom_ext
          · apply coprod.hom_ext
            · simp [hilbert_one_value, Two.constant]
            · simp [hilbert_two_value, Two.constant]
          · simp [hilbert_three_value, Two.constant]
        · simp [hilbert_instantiation_value, Two.constant]
      · simp [hilbert_distribution_value, Two.constant]
    · simp [hilbert_reflexivity_value, Two.constant]
  · simp [hilbert_equality_value, Two.constant]

end CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation
