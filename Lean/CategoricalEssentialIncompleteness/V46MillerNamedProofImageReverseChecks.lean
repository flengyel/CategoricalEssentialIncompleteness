/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageReverse


/-! # Statement checks in `V46MillerNamedProofImageReverseChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d
example (p : Total.underlying.obj (NamedProofImage.proofObject P σ π d Γ hΓ)) :
    FiniteAxiomProof σ π d Γ (NamedProofImage.decodeFormula P σ π d
      (Total.underlying.map (NamedProofImage.conclusion P σ π d Γ hΓ) p)) :=
  NamedProofImage.conclusion_finite P σ π d Γ hΓ p
example (φ : Fm) : NamedPostfixEncoding.formulaCode φ∈Total.Subobjects.imageCodes
    (NamedProofImage.conclusion P σ π d Γ hΓ) ↔ FiniteAxiomProof σ π d Γ φ :=
  NamedProofImage.formula_range_iff P σ π d Γ hΓ φ
example (φ : Fm) (hc : φ.freeVariables=[]) :
    (NamedProofImage.sentencePoint P σ π d φ hc).val∈Total.Subobjects.imageCodes
      (NamedProofImage.sentenceConclusion P σ π d Γ hΓ) ↔ FiniteAxiomProof σ π d Γ φ :=
  NamedProofImage.sentence_range_iff P σ π d Γ hΓ φ hc
example (φ : Fm) : NamedPostfixEncoding.formulaCode φ∈Total.Subobjects.imageCodes
    (NamedProofImage.sentenceConclusion P σ π d Γ hΓ ≫ NamedProofImage.sentenceWord P σ π d) ↔
      FiniteAxiomProof σ π d Γ φ ∧ φ.freeVariables=[] :=
  NamedProofImage.sentence_word_range_iff P σ π d Γ hΓ φ
example (φ : Fm) : NamedPostfixEncoding.formulaCode φ∈Total.support
    (NamedProofImage.formulaIdem P σ π d Γ hΓ) ↔ FiniteAxiomProof σ π d Γ φ :=
  NamedProofImage.formulaIdem_literal P σ π d Γ hΓ φ

/-- The literal sentence-word comparison exposes the actual finite support. -/
example (φ : Fm) : NamedPostfixEncoding.formulaCode φ∈Total.Subobjects.imageCodes
    (NamedProofImage.sentenceConclusion P σ π d Γ hΓ ≫ NamedProofImage.sentenceWord P σ π d) ↔
      (∃ L : List ℕ,(∀ code∈L,code∈Γ) ∧
        SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ) ∧ φ.freeVariables=[] :=
  NamedProofImage.sentence_word_range_iff P σ π d Γ hΓ φ

example (φ : Fm) :
    (∃ p : Total.underlying.obj (NamedProofImage.proofObject P σ π d Γ hΓ),
      Total.underlying.map (NamedProofImage.conclusion P σ π d Γ hΓ) p=
        NamedProofImage.formulaPoint P σ π d φ) ↔ FiniteAxiomProof σ π d Γ φ :=
  NamedProofImage.realizes_iff_finite P σ π d Γ hΓ φ

example (φ : Fm) : NamedPostfixEncoding.formulaCode φ∈Total.Subobjects.imageCodes
    (image.ι (NamedProofImage.conclusion P σ π d Γ hΓ)) ↔ FiniteAxiomProof σ π d Γ φ :=
  NamedProofImage.formula_image_iff P σ π d Γ hΓ φ

example (φ : Fm) (hc : φ.freeVariables=[]) :
    (NamedProofImage.sentencePoint P σ π d φ hc).val∈Total.Subobjects.imageCodes
      (image.ι (NamedProofImage.sentenceConclusion P σ π d Γ hΓ)) ↔ FiniteAxiomProof σ π d Γ φ :=
  NamedProofImage.sentence_image_iff P σ π d Γ hΓ φ hc

example (φ : Fm) (hc : φ.freeVariables=[]) :
    (NamedProofImage.sentencePoint P σ π d φ hc).val∈Total.support
      (NamedProofImage.sentenceIdem P σ π d Γ hΓ) ↔ FiniteAxiomProof σ π d Γ φ :=
  NamedProofImage.sentenceIdem_literal P σ π d Γ hΓ φ hc
