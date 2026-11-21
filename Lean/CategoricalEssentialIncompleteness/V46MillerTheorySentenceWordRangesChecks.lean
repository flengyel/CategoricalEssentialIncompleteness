/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTheorySentenceWordRanges


/-! # Gamma theorem and refutation ranges in sentence coordinates -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWordRanges
open OrderedFieldSyntax TheorySentenceWords

example (P : Uniform.Family) (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (·∈Γ)) (φ : Formula) : formulaCode φ∈Total.Subobjects.imageCodes
    (NamedProofImage.sentenceConclusion P functionSymbols relationSymbols bound Γ hΓ ≫
      (sentenceIso P).hom) ↔
      (∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (finiteCarrier L) φ) ∧ φ.freeVariables=[] :=
  theorem_word_iff P Γ hΓ φ

example (P : Uniform.Family) (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (·∈Γ)) (φ : Formula) : formulaCode φ∈Total.support
    (Idem.pull (literalNegation P).hom
      (Ranges.range (NamedProofImage.sentenceConclusion P functionSymbols relationSymbols bound Γ hΓ ≫
        (sentenceIso P).hom).hom)) ↔
      (∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (finiteCarrier L) (.neg φ)) ∧ φ.freeVariables=[] :=
  refutation_word_iff P Γ hΓ φ

example (P : Uniform.Family) : Total.support (⊤ : Idem (literalObject P).obj)=
    {word | OrderedFieldSyntax.sentencePredicate.val.Evalb ![word]} := literal_top_support P

example (P : Uniform.Family) (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (·∈Γ)) :
    Total.Subobjects.imageCodes (NamedProofImage.sentenceConclusion P functionSymbols relationSymbols bound Γ hΓ ≫
      (sentenceIso P).hom) = {word | ∃ φ : Formula, formulaCode φ=word ∧ φ.freeVariables=[] ∧
        (∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
          functionSymbols relationSymbols bound (finiteCarrier L) φ)} := theorem_words P Γ hΓ

example (P : Uniform.Family) (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (·∈Γ)) (φ : Formula) :
    formulaCode φ∈Total.Subobjects.imageCodes (image.ι
      (NamedProofImage.sentenceConclusion P functionSymbols relationSymbols bound Γ hΓ ≫ (sentenceIso P).hom)) ↔
      (∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (finiteCarrier L) φ) ∧ φ.freeVariables=[] :=
  regularImage_word_iff P Γ hΓ φ

end CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWordRanges
