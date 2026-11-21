/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedGammaEvidenceSoundness


/-! # Gamma theorem/refutation disjointness from its semantic model -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits Filter
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedGammaEvidenceSoundness
open NamedPostfixEncoding SyntacticSyntax SyntacticGeneratedAxioms
section
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
example {A B C : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ C) (b : Obj T M B) :
    (imageCarrier (chosenGraph T f).graph).val.Evalb ![((F T M).map g b).val] ↔
      b ∈ Set.range ((F T M).map (pullback.snd f g)) := image_pullback_point T M f g b
example : F T M ≅ realization T ⋙ PredicateInterpretation.canonicalDomainFunctor T M :=
  modelCodeComparison T M
end
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (H : PredicateCategory T ⥤ Type)
    (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
    {X : PredicateCategory T}
    (ax : @Quiver.Hom (PredicateCategory T) inferInstance X
      (plainCategoricalSyntax T V σ π d).sentenceObject) :
    Set.range (H.map (FirstOrderModelSoundness.sentenceConclusion T
      (plainCategoricalSyntax T V σ π d) ax)) =
      Set.range (H.map (SyntacticGeneratedTheory.sentenceConclusion T V σ π d ax)) :=
  sentence_range_plain T H V σ π d ax
universe w
section
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) (A : Carrier)
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
variable {K : Type w} [Nonempty K]
variable (f : ∀ n : Fin (d+1), Symbols σ n.val → (Fin n.val → K) → K)
variable (r : ∀ n : Fin (d+1), Symbols π n.val → (Fin n.val → K) → Prop)
variable (ρ : ℕ → K) (hA : NamedGammaSoundness.Models σ π d A f r ρ)
example (word : ℕ) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word] ∧
      (literalRefutationCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word]) :=
  standard_word_disjoint σ π d A f r ρ hA word
example {I : Type} (U : Ultrafilter I) (word : ArithmeticUltrapower.Model U) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word] ∧
      (literalRefutationCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word]) :=
  ultrapower_word_disjoint σ π d A f r ρ hA U word
end
open NamedArithmeticSignature
example (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : FFL.Entailment.Consistent (ArithmeticNamedProofConnectives.system A)) :
    Disjoint
      {word : ℕ | (literalTheoremCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word]}
      {word : ℕ | (literalRefutationCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word]} :=
  consistent_standard_disjoint A hPA hc
example (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : FFL.Entailment.Consistent (ArithmeticNamedProofConnectives.system A))
    {I : Type} (U : Ultrafilter I) (word : ArithmeticUltrapower.Model U) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word] ∧
      (literalRefutationCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word]) :=
  consistent_ultrapower_word_disjoint A hPA hc U word
example (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : FFL.Entailment.Consistent (ArithmeticNamedProofConnectives.system A)) (word : ℕ)
    (hs : (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound).val.Evalb ![word]) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb ![word] ∧
      (literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb
        ![NamedArithmeticProofSearch.negationWord ℕ word]) :=
  standard_sentence_evidence_disjoint A hPA hc word hs
example (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : FFL.Entailment.Consistent (ArithmeticNamedProofConnectives.system A))
    {I : Type} (U : Ultrafilter I) (word : ArithmeticUltrapower.Model U)
    (hs : (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound).val.Evalb ![word]) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb ![word] ∧
      (literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb
        ![NamedArithmeticProofSearch.negationWord (ArithmeticUltrapower.Model U) word]) :=
  ultrapower_sentence_evidence_disjoint A hPA hc U word hs
end CategoricalEssentialIncompleteness.V46.NamedGammaEvidenceSoundness
