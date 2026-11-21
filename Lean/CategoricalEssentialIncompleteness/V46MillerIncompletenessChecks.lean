/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerIncompleteness


/-! # The Miller theory in recursive sentence coordinates -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Incompleteness
open OrderedFieldSyntax

example (P : Uniform.Family) :
    CarrierIdempotents.SplitCarrier
      (NamedProofImage.syntaxData P functionSymbols relationSymbols bound).sentenceObject.obj ≅
    CarrierIdempotents.SplitCarrier (TheorySentenceWords.literalObject P).obj := splitSentenceIso P

example (P : Uniform.Family)
    (c d : Idem (CarrierIdempotents.SplitCarrier (TheorySentenceWords.literalObject P).obj))
    (h : Complementary c d) :
    Complementary (recoverIdem P c) (recoverIdem P d) ∧
      chartIdemIso P (recoverIdem P c)=c ∧ chartIdemIso P (recoverIdem P d)=d :=
  ⟨recover_complementary P c d h,chart_recover P c,chart_recover P d⟩

example (a : Point) (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ)) :
    (theoremIdem a Γ hΓ).hom=(splitSentenceIso (Uniform.Family.ofPoint a)).inv ≫
      (TheoryDomainApplication.theoremIdem a Γ hΓ).hom ≫
        (splitSentenceIso (Uniform.Family.ofPoint a)).hom := theorem_conjugacy_hom a Γ hΓ

example (a : Point) (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ)) :
    (refutationIdem a Γ hΓ).hom=(splitSentenceIso (Uniform.Family.ofPoint a)).inv ≫
      (Idem.pull (TheoryDomainApplication.negation a) (TheoryDomainApplication.theoremIdem a Γ hΓ)).hom ≫
        (splitSentenceIso (Uniform.Family.ofPoint a)).hom := refutation_conjugacy_hom a Γ hΓ

example (a : Point) (n : ℕ) :
    (theta a).hom.val n=Part.some (formulaCode (lt (mul (natural 2) (c n)) one)) := theta_value a n

example (a : Point) (word : ℕ) (hw : OrderedFieldSyntax.sentencePredicate.val.Evalb ![word]) :
    (nu a).hom.val word=Part.some (negationWord word) := nu_value a word hw

example : PrimrecPred (fun word : ℕ => OrderedFieldSyntax.sentencePredicate.val.Evalb ![word]) :=
  OrderedFieldSentenceMembership.sentence_membership_primrec

example (a : Point) (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (φ : Formula) : formulaCode φ∈CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔
      (∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (finiteCarrier L) φ) ∧ φ.freeVariables=[] :=
  theorem_word_iff a Γ hΓ φ

example (a : Point) (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (φ : Formula) : formulaCode φ∈CarrierIdempotents.support
      (Idem.pull (nu a) (theoremIdem a Γ hΓ)) ↔
      (∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (finiteCarrier L) (.neg φ)) ∧ φ.freeVariables=[] :=
  refutation_word_iff a Γ hΓ φ

example (a : Point) (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : ∀ φ : Formula,formulaCode φ∈RealClosedAxioms.theoryAxioms a →
      FiniteAxiomProof functionSymbols relationSymbols bound Γ φ)
    (hcons : ∀ φ : Formula,φ.freeVariables=[] → ¬(FiniteAxiomProof functionSymbols relationSymbols bound Γ φ ∧
      FiniteAxiomProof functionSymbols relationSymbols bound Γ (.neg φ))) :
    Inseparable (theoremIdem a Γ hΓ) (Idem.pull (nu a) (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ ⊔ Idem.pull (nu a) (theoremIdem a Γ hΓ)≠⊤ :=
  essential_incompleteness a ha Γ hΓ hext hcons

example (a : Point) (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : ∀ φ : Formula,formulaCode φ∈RealClosedAxioms.theoryAxioms a →
      FiniteAxiomProof functionSymbols relationSymbols bound Γ φ)
    (hcons : ∀ φ : Formula,φ.freeVariables=[] → ¬(FiniteAxiomProof functionSymbols relationSymbols bound Γ φ ∧
      FiniteAxiomProof functionSymbols relationSymbols bound Γ (.neg φ))) :
    ∃ φ : Formula,φ.freeVariables=[] ∧
      ¬(∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (finiteCarrier L) φ) ∧
      ¬(∃ L : List ℕ,(∀ c∈L,c∈Γ) ∧ SyntacticNamedHilbert.Derives
        functionSymbols relationSymbols bound (finiteCarrier L) (.neg φ)) :=
  native_incomplete a ha Γ hΓ hext hcons

example (a : Point) (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : ∀ φ : Formula,formulaCode φ∈RealClosedAxioms.theoryAxioms a →
      FiniteAxiomProof functionSymbols relationSymbols bound Γ φ)
    (hcons : theoremIdem a Γ hΓ ⊓ Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ) (Idem.pull (nu a) (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ ⊔ Idem.pull (nu a) (theoremIdem a Γ hΓ)≠⊤ :=
  printed_essential_incompleteness a ha Γ hΓ hext hcons

example (a : Point) (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈Γ))
    (hext : ∀ φ : Formula,formulaCode φ∈RealClosedAxioms.theoryAxioms a →
      FiniteAxiomProof functionSymbols relationSymbols bound Γ φ)
    (hcons : theoremIdem a Γ hΓ ⊓ Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    ∃ φ : Formula,φ.freeVariables=[] ∧ ¬RealClosedBounds.Proof Γ φ ∧
      ¬RealClosedBounds.Proof Γ (.neg φ) :=
  printed_native_incomplete a ha Γ hΓ hext hcons

example (a : Point) (ha : IsMiller a) : ∃ φ : Formula,φ.freeVariables=[] ∧
    ¬FiniteAxiomProof functionSymbols relationSymbols bound (RealClosedAxioms.theoryAxioms a) φ ∧
    ¬FiniteAxiomProof functionSymbols relationSymbols bound (RealClosedAxioms.theoryAxioms a) (.neg φ) :=
  base_native_incomplete a ha

end CategoricalEssentialIncompleteness.V46.Miller.Incompleteness
