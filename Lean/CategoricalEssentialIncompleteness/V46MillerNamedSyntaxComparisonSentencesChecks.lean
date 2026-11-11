/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSentences


/-! # Statement checks in `V46MillerNamedSyntaxComparisonSentencesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax V σ π d
local notation "S₁" => NamedSyntaxComparison.presentedSyntax P V σ π d
local notation "F" => Syntax.predicateFunctor P

example : IsPullback
    ((F).map (S₀).sentenceInclusion ≫ (NamedSyntaxComparison.formulaIso P V σ π d).inv)
    ((F).map (pullback.snd (S₀).formulaOccurrences (S₀).lists.algebra.nil) ≫ terminalComparison (F))
    (S₁).formulaOccurrences (S₁).lists.algebra.nil :=
  NamedSyntaxComparison.sentenceComparisonPullback P V σ π d

example : (F).obj (S₀).sentenceObject ≅ (S₁).sentenceObject :=
  NamedSyntaxComparison.mappedSentenceIso P V σ π d

example : (NamedSyntaxComparison.mappedSentenceIso P V σ π d).hom ≫ (S₁).sentenceInclusion =
    (F).map (S₀).sentenceInclusion ≫ (NamedSyntaxComparison.formulaIso P V σ π d).inv :=
  NamedSyntaxComparison.mappedSentenceIso_inclusion P V σ π d

example : (S₁).sentenceObject ≅ (Syntax.predicateFunctor P).obj (S₀).sentenceObject :=
  NamedSyntaxComparison.sentenceIso P V σ π d
example : (NamedSyntaxComparison.sentenceIso P V σ π d).hom ≫
    (Syntax.predicateFunctor P).map (S₀).sentenceInclusion=
      (S₁).sentenceInclusion ≫ (NamedSyntaxComparison.formulaIso P V σ π d).hom :=
  NamedSyntaxComparison.sentenceIso_inclusion P V σ π d
example : (NamedSyntaxComparison.sentenceIso P V σ π d).inv ≫ (S₁).sentenceInclusion=
    (Syntax.predicateFunctor P).map (S₀).sentenceInclusion ≫ (NamedSyntaxComparison.formulaIso P V σ π d).inv :=
  NamedSyntaxComparison.sentenceIso_inverse_inclusion P V σ π d

example : (NamedSyntaxComparison.formulaIso P V σ π d).hom ≫ (F).map (S₀).negationConstructor =
    (S₁).negationConstructor ≫ (NamedSyntaxComparison.formulaIso P V σ π d).hom :=
  NamedSyntaxComparison.formula_negation_comparison P V σ π d

example : (NamedSyntaxComparison.sentenceIso P V σ π d).hom ≫
    (Syntax.predicateFunctor P).map (S₀).sentenceNegation=
      (S₁).sentenceNegation ≫ (NamedSyntaxComparison.sentenceIso P V σ π d).hom :=
  NamedSyntaxComparison.sentence_negation_comparison P V σ π d

-- Sentence point codes reach literal formula words only through these maps.
example (point word : ℕ) :
    word ∈ Total.val ((S₁).sentenceInclusion ≫
      (NamedSyntaxComparison.formulaIso P V σ π d).hom).hom point ↔
      ∃ q : PredicateInterpretation.Obj ℕ (S₀).sentenceObject,
        q.val ∈ Total.val (NamedSyntaxComparison.sentenceIso P V σ π d).hom.hom point ∧
          ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map (S₀).sentenceInclusion q).val = word :=
  NamedSyntaxComparison.sentenceInclusion_graph P V σ π d point word
