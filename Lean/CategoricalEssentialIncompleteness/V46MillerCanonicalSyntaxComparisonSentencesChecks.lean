/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonSentences


/-! # Chosen sentence pullbacks and arbitrary external Γ after the push -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable (a : Point) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → Carrier) (d : ℕ)
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (Uniform.Family.ofPoint a) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d
example : (S₂).sentenceObject ≅ (E).functor.obj (S₁).sentenceObject := sentenceIso a V σ π d
example : (sentenceIso a V σ π d).hom ≫ (E).functor.map (S₁).sentenceInclusion =
    (S₂).sentenceInclusion ≫ (formulaIso a V σ π d).inv := sentenceIso_inclusion a V σ π d
example : (E).functor.map (S₁).sentenceNegation ≫ (mappedSentenceIso a V σ π d).hom =
    (mappedSentenceIso a V σ π d).hom ≫ (S₂).sentenceNegation := sentenceNegation_comparison a V σ π d
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (· ∈ Γ))
example : Mono (canonicalAxioms a σ π d Γ hΓ) := inferInstance
example : canonicalAxioms a σ π d Γ hΓ ≫ canonicalSentenceWord a σ π d =
    (E).functor.map (NamedProofImage.axioms (Uniform.Family.ofPoint a) σ π d Γ hΓ ≫
      NamedProofImage.sentenceWord (Uniform.Family.ofPoint a) σ π d) := canonicalAxioms_word a σ π d Γ hΓ
example : IsPullback
    ((E).functor.map (S₁).sentenceInclusion ≫ (formulaIso a V σ π d).hom)
    ((E).functor.map (pullback.snd (S₁).formulaOccurrences (S₁).lists.algebra.nil) ≫
      (DecidableVariables.Transport.terminalIso (E)).hom)
    (S₂).formulaOccurrences (S₂).lists.algebra.nil :=
  canonicalSentencePullback a V σ π d

local notation "Vn" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
example : IsPullback (canonicalAxioms a σ π d Γ hΓ)
    ((E).functor.map (SentenceAxiomPullbacks.wordProjection
      (NamedProofImage.sentenceWord (Uniform.Family.ofPoint a) σ π d) Γ hΓ))
    (canonicalSentenceWord a σ π d)
    ((E).functor.map (AxiomSubobjects.axiomInclusion (Uniform.Family.ofPoint a)
      (NamedSyntaxComparison.sourceSyntax (Vn) σ π d).algebra.a.2 Γ hΓ)) :=
  canonicalAxiomPullback a σ π d Γ hΓ

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
