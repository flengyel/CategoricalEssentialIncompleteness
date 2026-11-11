/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSentences


/-! # Statement checks in `V46NumericalNamedLiteralSentencesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSentencesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d

example : IsPullback ((E).functor.map (S₀).sentenceInclusion ≫ (literalFormulaIso V σ π d).hom)
    ((E).functor.map (pullback.snd (S₀).formulaOccurrences (S₀).lists.algebra.nil) ≫
      (DecidableVariables.Transport.terminalIso E).hom)
    (S₁).formulaOccurrences (S₁).lists.algebra.nil := literalSentence_isPullback V σ π d

example : (literalSentenceIso V σ π d).hom ≫ (S₁).sentenceInclusion =
    (E).functor.map (S₀).sentenceInclusion ≫ (literalFormulaIso V σ π d).hom :=
  literalSentenceIso_inclusion V σ π d

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSentencesChecks
