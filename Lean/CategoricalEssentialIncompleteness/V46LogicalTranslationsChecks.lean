/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalTranslations

/-! # Statement checks for logical translations -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.FirstOrderPresentation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {P Q R : FirstOrderPresentation V}

example (σ : Translation P Q) :
    P.syntaxData.variableConstructor ≫ σ.term = Q.syntaxData.variableConstructor := σ.variable_law

example (σ : Translation P Q) :
    ∃ s : P.syntaxData.admissibleSubstitution ⟶ Q.syntaxData.admissibleSubstitution,
      s ≫ Q.syntaxData.admissibleInclusion = P.syntaxData.admissibleInclusion ≫
        prod.map σ.formula (prod.map (𝟙 V) σ.term) ∧
      s ≫ Q.syntaxData.formulaSubstitution = P.syntaxData.formulaSubstitution ≫ σ.formula :=
  σ.substitution

example (σ : Translation P Q) :
    ∃ ρ : RulePresentation.Translation P.logicalRuleData Q.logicalRuleData,
      ρ.formula = σ.formula := σ.preserves_logical_rules

example (σ : Translation P Q) :
    P.syntaxData.sentenceNegation ≫ σ.sentence = σ.sentence ≫ Q.syntaxData.sentenceNegation :=
  σ.sentence_negation

example (σ : Translation P Q) (A : Subobject P.syntaxData.sentenceObject)
    (B : Subobject Q.syntaxData.sentenceObject) (k : (A : D) ⟶ (B : D))
    (hk : k ≫ B.arrow = A.arrow ≫ σ.sentence) :
    RulePresentation.Translation (P.syntaxData.logicalRules A.arrow)
      (Q.syntaxData.logicalRules B.arrow) := σ.rulesMap A B k hk

example (σ : P ⟶ Q) (τ : Q ⟶ R) :
    ((σ ≫ τ) : P ⟶ R).sentence = σ.sentence ≫ τ.sentence := rfl

#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.comp
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.preserves_logical_rules
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.rulesMap
#print axioms CategoricalEssentialIncompleteness.V46.FirstOrderPresentation.Translation.sentence_negation
