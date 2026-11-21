/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageData


/-! # Named points, arbitrary external axioms and constructed proofs -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "S" => NamedProofImage.syntaxData P σ π d
example (t : Tm) : (NamedProofImage.termPoint P σ π d t).val=NamedPostfixEncoding.termCode t :=
  NamedProofImage.termPoint_value P σ π d t
example (φ : Fm) : (NamedProofImage.formulaPoint P σ π d φ).val=NamedPostfixEncoding.formulaCode φ :=
  NamedProofImage.formulaPoint_value P σ π d φ
example (φ : Fm) (hc : φ.freeVariables=[]) :
    Total.underlying.map (S).sentenceInclusion (NamedProofImage.sentencePoint P σ π d φ hc)=
      NamedProofImage.formulaPoint P σ π d φ :=
  NamedProofImage.sentencePoint_inclusion P σ π d φ hc
example (φ : Fm) (hc : φ.freeVariables=[]) :
    NamedPostfixEncoding.formulaCode φ∈Total.val (NamedProofImage.sentenceWord P σ π d).hom
      (NamedProofImage.sentencePoint P σ π d φ hc).val :=
  NamedProofImage.sentencePoint_word P σ π d φ hc
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
example (φ : Fm) (hc : φ.freeVariables=[]) (hφ : NamedPostfixEncoding.formulaCode φ∈Γ) :
    Total.underlying.map (NamedProofImage.axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion)
      (NamedProofImage.axiomPoint P σ π d Γ hΓ φ hc hφ)=NamedProofImage.formulaPoint P σ π d φ :=
  NamedProofImage.axiomPoint_formula P σ π d Γ hΓ φ hc hφ
example : IsInitial (NamedProofImage.proofAlgebra P σ π d Γ hΓ) :=
  NamedProofImage.proofInitial P σ π d Γ hΓ
example : NamedProofImage.sentenceProofObject P σ π d Γ hΓ=
    pullback (NamedProofImage.conclusion P σ π d Γ hΓ) (S).sentenceInclusion := rfl
