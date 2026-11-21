/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityExponential
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersPresentation

/-! # The numeral-fiber comparison for uniform provability -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
open NamedArithmeticSignature

private theorem natural_apply {D : Type u} [Category.{v} D]
    (F G : D ⥤ Type) (η : F ≅ G) {X Y : D} (f : X ⟶ Y) (x : F.obj X) :
    (η.app Y).toEquiv (F.map f x) = G.map f ((η.app X).toEquiv x) :=
  ConcreteCategory.congr_hom (η.hom.naturality f) x

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "H" => PredicateInterpretation.totalFunctor 𝗣𝗔 M
local notation "E" => realization 𝗣𝗔

def sentencePoint (z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    (H).obj ArithmeticIndexedAxioms.sentence :=
  ((PredicateInterpretation.predicateComparison 𝗣𝗔 M).app
    ArithmeticIndexedAxioms.sentencePredicate).toEquiv.symm ⟨z,hs⟩

theorem sentencePoint_value (z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    (((PredicateInterpretation.predicateComparison 𝗣𝗔 M).hom.app
      ArithmeticIndexedAxioms.sentencePredicate) (sentencePoint M z hs)).val = z :=
  congrArg Subtype.val (((PredicateInterpretation.predicateComparison 𝗣𝗔 M).app
    ArithmeticIndexedAxioms.sentencePredicate).toEquiv.apply_symm_apply ⟨z,hs⟩)

/-- The product point is the interpreted numeral leg. This uses its constructor-preserving
categorical equality, not an arbitrary fiber chart. -/
theorem productPoint_numeral (e : ℕ) (z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    productPoint M (e : M) z hs =
      (H).map (ArithmeticIndexedFibers.fiberMap e ArithmeticIndexedAxioms.sentence)
        (sentencePoint M z hs) := by
  let x : Obj 𝗣𝗔 M ArithmeticIndexedAxioms.sentencePredicate := ⟨z,hs⟩
  let r := ArithmeticIndexedFibers.rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e
  have hr : (F 𝗣𝗔 M).map r x = rawPairPoint M (e : M) z hs :=
    Subtype.ext (ArithmeticIndexedFibers.rawNumeralPair_value M
      ArithmeticIndexedAxioms.sentencePredicate e x)
  have hn := natural_apply (F 𝗣𝗔 M) ((E) ⋙ (H))
    (PredicateInterpretation.predicateComparison 𝗣𝗔 M).symm r x
  have hc := congrArg ((H).map ArithmeticIndexedAxioms.productIso.hom) hn
  have hcomp : (H).map ArithmeticIndexedAxioms.productIso.hom
      ((H).map ((E).map r) (sentencePoint M z hs)) =
      (H).map ((E).map r ≫ ArithmeticIndexedAxioms.productIso.hom) (sentencePoint M z hs) :=
    (congrArg (fun f => f (sentencePoint M z hs))
      ((H).map_comp ((E).map r) ArithmeticIndexedAxioms.productIso.hom)).symm
  have he := congrArg (fun f => (H).map f (sentencePoint M z hs))
    (ArithmeticIndexedFibers.realized_rawNumeralPair e)
  exact (congrArg (productChart M) hr.symm).trans (hc.trans (hcomp.trans he))

theorem provability_fiber (AxPA : Carrier) (e : ℕ) (z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    (provability AxPA).val.Evalb ![(e : M),z] ↔
      ∃ p : (H).obj (ArithmeticIndexedFibers.individualSentenceProof AxPA e),
        (H).map (ArithmeticIndexedFibers.individualSentenceConclusion AxPA e) p =
          sentencePoint M z hs := by
  have hpoint := productPoint_numeral M e z hs
  have he : (∃ p : (H).obj (ArithmeticIndexedFamily.sentenceProof AxPA),
      (H).map (ArithmeticIndexedFamily.sentenceConclusion AxPA) p = productPoint M (e : M) z hs) ↔
      ∃ p : (H).obj (ArithmeticIndexedFamily.sentenceProof AxPA),
        (H).map (ArithmeticIndexedFamily.sentenceConclusion AxPA) p =
          (H).map (ArithmeticIndexedFibers.fiberMap e ArithmeticIndexedAxioms.sentence)
            (sentencePoint M z hs) :=
    exists_congr (fun p => Iff.of_eq (congrArg (fun q =>
      (H).map (ArithmeticIndexedFamily.sentenceConclusion AxPA) p = q) hpoint))
  exact (provability_model M AxPA (e : M) z hs).trans (he.trans
    (range_pullback_point (H) (ArithmeticIndexedFibers.sentenceMap AxPA e)
      (ArithmeticIndexedFibers.individualSentenceConclusion AxPA e)
      (ArithmeticIndexedFamily.sentenceConclusion AxPA)
      (ArithmeticIndexedFibers.fiberMap e ArithmeticIndexedAxioms.sentence)
      (ArithmeticIndexedFibers.sentence_pullback AxPA e) (sentencePoint M z hs)))

private theorem literal_theorem_sentence (A : Carrier) (z : M)
    (h : (ArithmeticLiteralModel.theoremPredicate A).val.Evalb ![z]) :
    NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z] :=
  ((SyntacticGeneratedAxioms.theoremCarrier_model 𝗣𝗔 variableSymbols functionSymbols
    relationSymbols bound M A z).mp
    ((SyntacticGeneratedAxioms.literalTheoremCarrier_model 𝗣𝗔 variableSymbols functionSymbols
      relationSymbols bound M A z).mp h)).1

private theorem provability_numeral_guarded (AxPA : Carrier) (e : ℕ) (z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    (provability AxPA).val.Evalb ![(e : M),z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![z] := by
  have hOld := ArithmeticIndexedFibers.individual_oldGamma_model AxPA e M (sentencePoint M z hs)
  have hval := sentencePoint_value M z hs
  have hv := Iff.of_eq (congrArg (fun w : M =>
    (ArithmeticLiteralModel.theoremPredicate (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![w]) hval)
  exact (provability_fiber M AxPA e z hs).trans (hOld.symm.trans hv)

/-- The uniform formula represents the given Gamma_e theorem program in every PA model, on
every internal sentence-code input. -/
theorem provability_numeral (AxPA : Carrier) (e : ℕ) (z : M) :
    (provability AxPA).val.Evalb ![(e : M),z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![z] := by
  constructor
  · intro hp
    exact (provability_numeral_guarded M AxPA e z (provability_sentence M AxPA (e : M) z hp)).mp hp
  · intro ht
    exact (provability_numeral_guarded M AxPA e z
      (literal_theorem_sentence M (ArithmeticIndexedAxioms.fiberAxioms AxPA e) z ht)).mpr ht

/-- The selected-program definition of Prov has the same numeral fiber, on every internal
word of every PA model. -/
theorem programProvability_numeral (AxPA : Carrier) (e : ℕ) (z : M) :
    (programProvability AxPA).val.Evalb ![(e : M),z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![z] :=
  (programProvability_eval M AxPA (e : M) z).trans (provability_numeral M AxPA e z)

/-- Exponential object-code transport gives the selected-program predicate the same
numeral fiber, universally in PA models. -/
theorem printedProvability_numeral (AxPA : Carrier) (e : ℕ) (z : M) :
    (printedProvability AxPA).val.Evalb ![(e : M),z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![z] :=
  (printedProvability_eval M AxPA (e : M) z).trans (provability_numeral M AxPA e z)

/-- The PA sentence quantifies over every internal formula word. -/
def numeralComparisonSentence (AxPA : Carrier) (e : ℕ) : ArithmeticSentence :=
  let P := provability AxPA
  let Q := SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
    relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)
  “∀ z, !P.val !!(e) z ↔ !Q.val z”

theorem provability_numeral_PA (AxPA : Carrier) (e : ℕ) :
    𝗣𝗔 ⊢ numeralComparisonSentence AxPA e := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,numeralComparisonSentence,numeral_eq_natCast_app] using provability_numeral M AxPA e

def programNumeralComparisonSentence (AxPA : Carrier) (e : ℕ) : ArithmeticSentence :=
  let P := programProvability AxPA
  let Q := SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
    relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)
  “∀ z, !P.val !!(e) z ↔ !Q.val z”

theorem programProvability_numeral_PA (AxPA : Carrier) (e : ℕ) :
    𝗣𝗔 ⊢ programNumeralComparisonSentence AxPA e := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,programNumeralComparisonSentence,numeral_eq_natCast_app] using
    programProvability_numeral M AxPA e

def printedNumeralComparisonSentence (AxPA : Carrier) (e : ℕ) : ArithmeticSentence :=
  let P := printedProvability AxPA
  let Q := SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
    relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)
  “∀ z, !P.val !!(e) z ↔ !Q.val z”

theorem printedProvability_numeral_PA (AxPA : Carrier) (e : ℕ) :
    𝗣𝗔 ⊢ printedNumeralComparisonSentence AxPA e := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,printedNumeralComparisonSentence,numeral_eq_natCast_app] using
    printedProvability_numeral M AxPA e

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
