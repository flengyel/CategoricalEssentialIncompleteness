/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageForward


/-! # Statement checks in `V46MillerNamedProofImageForwardChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedFiniteSyntax NamedPostfixEncoding
open NamedProofImage
open NamedProofImage.Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P:=P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
example (L : List ℕ) (hL : ∀ x∈L,x∈Γ) {φ : Fm}
    (h : SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ) :
    ∃ p : (U).obj (proofObject P σ π d Γ hΓ),
      (U).map (conclusion P σ π d Γ hΓ) p=formulaPoint P σ π d φ :=
  native_realizes P σ π d Γ hΓ L hL h
example {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) :
    ∃ p : (U).obj (proofObject P σ π d Γ hΓ),
      (U).map (conclusion P σ π d Γ hΓ) p=formulaPoint P σ π d φ :=
  finite_realizes P σ π d Γ hΓ h
example {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) :
    formulaCode φ∈Total.Subobjects.imageCodes (conclusion P σ π d Γ hΓ) :=
  finite_formula_range P σ π d Γ hΓ h
example {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) :
    formulaCode φ∈Total.Subobjects.imageCodes (image.ι (conclusion P σ π d Γ hΓ)) :=
  finite_formula_image P σ π d Γ hΓ h
example {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) (hc : φ.freeVariables=[]) :
    ∃ p : (U).obj (sentenceProofObject P σ π d Γ hΓ),
      (U).map (sentenceConclusion P σ π d Γ hΓ) p=sentencePoint P σ π d φ hc :=
  finite_sentence_realizes P σ π d Γ hΓ h hc
example {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) (hc : φ.freeVariables=[]) :
    (sentencePoint P σ π d φ hc).val∈Total.Subobjects.imageCodes
      (image.ι (sentenceConclusion P σ π d Γ hΓ)) := finite_sentence_image P σ π d Γ hΓ h hc
example {φ : Fm} (h : FiniteAxiomProof σ π d Γ φ) (hc : φ.freeVariables=[]) :
    formulaCode φ∈Total.Subobjects.imageCodes
      (sentenceConclusion P σ π d Γ hΓ ≫ sentenceWord P σ π d) :=
  finite_sentence_word_range P σ π d Γ hΓ h hc
example (p : (U).obj ((Syntax.predicateFunctor P).obj (variableCarrier : PredicateCategory 𝗣𝗔) ⨯
      (S).algebra.a.2))
    (h : Realizes P σ π d Γ hΓ ((U).map prod.snd p)) :
    Realizes P σ π d Γ hΓ ((U).map (S).quantifierConstructor p) := generalization P σ π d Γ hΓ p h
example (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2))
    (hφ : Realizes P σ π d Γ hΓ ((U).map prod.fst p))
    (himp : Realizes P σ π d Γ hΓ ((U).map (S).implicationConstructor p)) :
    Realizes P σ π d Γ hΓ ((U).map prod.snd p) := modus_ponens P σ π d Γ hΓ p hφ himp
