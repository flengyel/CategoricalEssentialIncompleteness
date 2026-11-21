/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalProofComparison


/-! # The canonical Γ derivation algebra and generated sentence image -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable (a : Point) (σ π : ℕ → Carrier) (d : ℕ)
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (· ∈ Γ))
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₁" => NamedProofImage.syntaxData (P) σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (V) σ π d
example : IsInitial (canonicalProofAlgebra a σ π d Γ hΓ) := canonicalProofInitial a σ π d Γ hΓ
example : canonicalProofObject a σ π d Γ hΓ ≅
    (E).functor.obj (NamedProofImage.proofObject (P) σ π d Γ hΓ) := proofIso a σ π d Γ hΓ
example : (proofIso a σ π d Γ hΓ).hom ≫
      ((E).functor.map (NamedProofImage.conclusion (P) σ π d Γ hΓ) ≫ (formulaIso a (V) σ π d).hom) =
    canonicalConclusion a σ π d Γ hΓ := proofIso_conclusion a σ π d Γ hΓ
example : (canonicalProofAlgebra a σ π d Γ hΓ).str ≫ (proofOverIso a σ π d Γ hΓ).hom =
    (canonicalRules a σ π d Γ hΓ).inference.map (proofOverIso a σ π d Γ hΓ).hom ≫
      (mappedProofAlgebra a σ π d Γ hΓ).str := proof_constructor a σ π d Γ hΓ
example : (sentenceProofIso a σ π d Γ hΓ).hom ≫
      (E).functor.map (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ) =
    canonicalSentenceConclusion a σ π d Γ hΓ ≫ (sentenceIso a (V) σ π d).hom :=
  sentenceProofIso_conclusion a σ π d Γ hΓ
example : image (canonicalSentenceConclusion a σ π d Γ hΓ) ≅
    (E).functor.obj (image (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) := sentenceImageIso a σ π d Γ hΓ
example : imageSubobject (canonicalSentenceConclusion a σ π d Γ hΓ) =
    Subobject.mk ((E).functor.map (image.ι (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) ≫
      (mappedSentenceIso a (V) σ π d).hom) := canonical_sentenceTheory_eq a σ π d Γ hΓ
example (n : Fin 3) :
    (E).functor.map ((NamedProofImage.rules (P) σ π d Γ hΓ).premises n) ≫
      (Inference.formulaPower (E) (formulaIso a (V) σ π d) n.val).hom =
    (ruleCoefficient a σ π d Γ hΓ n).hom ≫ (canonicalRules a σ π d Γ hΓ).premises n :=
  rule_premises a σ π d Γ hΓ n

example (n : Fin 3) :
    (E).functor.map ((NamedProofImage.rules (P) σ π d Γ hΓ).conclusion n) ≫
      (formulaIso a (V) σ π d).hom =
    (ruleCoefficient a σ π d Γ hΓ n).hom ≫ (canonicalRules a σ π d Γ hΓ).conclusion n :=
  rule_conclusion a σ π d Γ hΓ n

example : (NamedProofImage.rules (P) σ π d Γ hΓ).inference ⋙
    (Inference.slice (E) (formulaIso a (V) σ π d)).functor ≅
      (Inference.slice (E) (formulaIso a (V) σ π d)).functor ⋙
        (canonicalRules a σ π d Γ hΓ).inference := inferenceIso a σ π d Γ hΓ

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
