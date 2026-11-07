/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticLiteralSignature
import CategoricalEssentialIncompleteness.V46NumericalArithmeticSignatureWords
import CategoricalEssentialIncompleteness.V46NumericalArithmeticAlgorithms
import CategoricalEssentialIncompleteness.V46NumericalArithmeticGeometry
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSentenceValues
import CategoricalEssentialIncompleteness.V46NumericalSentenceMorphisms
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Actual arithmetic formula and sentence coordinates

The comparisons preserve the named word. Each direction is a numerical
morphism, with a partial-recursive program total on its carrier.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Coordinates
open NamedArithmeticSignature NamedPostfixEncoding SyntacticSyntax

def functions (k : ℕ) : NumericalTuples.Object :=
  NumericalCoordinates.predicateObject (functionSymbols k : PredicateCategory 𝗧𝗔)
def relations (k : ℕ) : NumericalTuples.Object :=
  NumericalCoordinates.predicateObject (relationSymbols k : PredicateCategory 𝗧𝗔)

def numericalSyntax := NumericalNamed.literalCategoricalSyntax
  NumericalNamed.variableObject functions relations bound

def sourceSyntax := NumericalNamed.literalSourceSyntax
  NumericalNamed.variableObject functions relations bound

abbrev originalSyntax := ArithmeticLiteralModel.sentenceSyntax

def variableIso : NumericalNamed.variableObject ≅ numericalInterpretation.obj variableSymbols :=
  NumericalSentenceMorphisms.omegaIso

private def wordIso (C D : PredicateCategory 𝗧𝗔)
    (h : ∀ n : ℕ, C.val.Evalb ![n] ↔ D.val.Evalb ![n]) :
    NumericalCoordinates.predicateObject C ≅ NumericalCoordinates.predicateObject D where
  hom :=
    { toFun := fun x => ⟨x.val,(h x.val).mp x.property⟩
      represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩ }
  inv :=
    { toFun := fun x => ⟨x.val,(h x.val).mpr x.property⟩
      represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩ }
  hom_inv_id := NumericalTuples.Map.ext rfl
  inv_hom_id := NumericalTuples.Map.ext rfl

private theorem wordIso_hom_value (C D : PredicateCategory 𝗧𝗔)
    (h : ∀ n : ℕ, C.val.Evalb ![n] ↔ D.val.Evalb ![n])
    (x : NumericalTuples.Point (NumericalCoordinates.predicateObject C)) :
    ((wordIso C D h).hom.toFun x).val = x.val := rfl

private theorem wordIso_inv_value (C D : PredicateCategory 𝗧𝗔)
    (h : ∀ n : ℕ, C.val.Evalb ![n] ↔ D.val.Evalb ![n])
    (x : NumericalTuples.Point (NumericalCoordinates.predicateObject D)) :
    ((wordIso C D h).inv.toFun x).val = x.val := rfl

private theorem wordChart_inverse_value {A : NumericalTuples.Object} (C D : PredicateCategory 𝗧𝗔)
    (h : ∀ n : ℕ, C.val.Evalb ![n] ↔ D.val.Evalb ![n])
    (i : A ≅ NumericalCoordinates.predicateObject C)
    (x : NumericalTuples.Point (NumericalCoordinates.predicateObject D)) :
    (i.hom.toFun ((i ≪≫ wordIso C D h).inv.toFun x)).val = x.val := by
  have hi := congrArg (fun f => f.toFun ((wordIso C D h).inv.toFun x)) i.inv_hom_id
  exact (congrArg Subtype.val hi).trans (wordIso_inv_value C D h x)

private theorem term_membership (n : ℕ) :
    sourceSyntax.algebra.a.1.val.Evalb ![n] ↔ originalSyntax.algebra.a.1.val.Evalb ![n] := by
  change (Postfix.plainCarrier false
    (SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
      (LiteralSignature.coefficients functionSymbols) bound)
    (SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
      (LiteralSignature.coefficients relationSymbols) bound)).val.Evalb ![n] ↔
    (Postfix.plainCarrier false (termPolynomial functionSymbols bound)
      (formulaPolynomial relationSymbols bound)).val.Evalb ![n]
  exact (NumericalNamed.coded_plain_native (LiteralSignature.coefficients functionSymbols)
    (LiteralSignature.coefficients relationSymbols) bound false n).trans
      (SignatureRelabel.term_membership
        (σ := LiteralSignature.coefficients functionSymbols) (τ := functionSymbols)
        (π := LiteralSignature.coefficients relationSymbols) (ρ := relationSymbols) (d := bound)
        (fun k m => (LiteralSignature.coefficient_membership functionSymbols k m).symm) n)

private theorem formula_membership (n : ℕ) :
    sourceSyntax.algebra.a.2.val.Evalb ![n] ↔ originalSyntax.algebra.a.2.val.Evalb ![n] := by
  change (Postfix.plainCarrier true
    (SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
      (LiteralSignature.coefficients functionSymbols) bound)
    (SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
      (LiteralSignature.coefficients relationSymbols) bound)).val.Evalb ![n] ↔
    (Postfix.plainCarrier true (termPolynomial functionSymbols bound)
      (formulaPolynomial relationSymbols bound)).val.Evalb ![n]
  exact (NumericalNamed.coded_plain_native (LiteralSignature.coefficients functionSymbols)
    (LiteralSignature.coefficients relationSymbols) bound true n).trans
      (SignatureRelabel.formula_membership
        (σ := LiteralSignature.coefficients functionSymbols) (τ := functionSymbols)
        (π := LiteralSignature.coefficients relationSymbols) (ρ := relationSymbols) (d := bound)
        (fun k m => (LiteralSignature.coefficient_membership functionSymbols k m).symm)
        (fun k m => (LiteralSignature.coefficient_membership relationSymbols k m).symm) n)

/-- These are actual numerical isomorphisms onto the fixed PA named-word
carriers. The inverse coefficient formulas are compared, not identified. -/
def termIso : numericalSyntax.algebra.a.1 ≅ numericalInterpretation.obj originalSyntax.algebra.a.1 :=
  NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound ≪≫
    wordIso sourceSyntax.algebra.a.1 (originalSyntax.algebra.a.1 : PredicateCategory 𝗧𝗔) term_membership

def formulaIso : numericalSyntax.algebra.a.2 ≅ numericalInterpretation.obj originalSyntax.algebra.a.2 :=
  NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound ≪≫
    wordIso sourceSyntax.algebra.a.2 (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔) formula_membership

abbrev termIso_value (t : NumericalTuples.Point numericalSyntax.algebra.a.1) :=
  wordIso_hom_value sourceSyntax.algebra.a.1 (originalSyntax.algebra.a.1 : PredicateCategory 𝗧𝗔)
    term_membership
    ((NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound).hom.toFun t)

abbrev formulaIso_value (φ : NumericalTuples.Point numericalSyntax.algebra.a.2) :=
  wordIso_hom_value sourceSyntax.algebra.a.2 (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔)
    formula_membership
    ((NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound).hom.toFun φ)

abbrev termIso_inverse_value
    (t : NumericalTuples.Point (numericalInterpretation.obj originalSyntax.algebra.a.1)) :=
  wordChart_inverse_value (A := numericalSyntax.algebra.a.1)
    sourceSyntax.algebra.a.1 (originalSyntax.algebra.a.1 : PredicateCategory 𝗧𝗔) term_membership
    (NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound) t

abbrev formulaIso_inverse_value
    (φ : NumericalTuples.Point (numericalInterpretation.obj originalSyntax.algebra.a.2)) :=
  wordChart_inverse_value (A := numericalSyntax.algebra.a.2)
    sourceSyntax.algebra.a.2 (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔) formula_membership
    (NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound) φ

private def formulaSentence : numericalSyntax.sentenceObject ⟶
    numericalInterpretation.obj originalSyntax.algebra.a.2 :=
  numericalSyntax.sentenceInclusion ≫ formulaIso.hom

private theorem closed (s : NumericalTuples.Point numericalSyntax.sentenceObject) :
    ArithmeticLiteralModel.sentencePredicate.val.Evalb (M := ℕ) ![(formulaSentence.toFun s).val] := by
  have hv := (NumericalNamed.literal_sentence_iff
    NumericalNamed.variableObject functions relations bound
      (numericalSyntax.sentenceInclusion.toFun s)).mp ⟨s,rfl⟩
  apply (ConcreteNamedComparison.literalSentenceCarrier_eval
    𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ _).mpr
  refine ⟨(formulaSentence.toFun s).property,?_⟩
  change ConcreteNamedSubstitution.freeVariables (M := ℕ) variableSymbols functionSymbols relationSymbols
    bound (formulaIso.hom.toFun (numericalSyntax.sentenceInclusion.toFun s)).val = 0
  have hw := formulaIso_value (numericalSyntax.sentenceInclusion.toFun s)
  exact (congrArg (ConcreteNamedSubstitution.freeVariables (M := ℕ)
    variableSymbols functionSymbols relationSymbols bound) hw).trans
      ((Algorithms.freeVariables_signature (M := ℕ) variableSymbols
        (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
        functionSymbols (LiteralSignature.coefficients functionSymbols)
        relationSymbols (LiteralSignature.coefficients relationSymbols) bound _).trans hv)

/-- Corestriction reuses the program of the formula-word map. It does
not ask that program to halt outside the sentence carrier. -/
private def wordCorestriction {A : NumericalTuples.Object} (C D : PredicateCategory 𝗧𝗔)
    (f : A ⟶ NumericalCoordinates.predicateObject C)
    (hf : ∀ x : NumericalTuples.Point A, D.val.Evalb (M := ℕ) ![(f.toFun x).val]) :
    A ⟶ NumericalCoordinates.predicateObject D where
  toFun x := ⟨(f.toFun x).val,hf x⟩
  represented := f.represented

private theorem wordCorestriction_value {A : NumericalTuples.Object} (C D : PredicateCategory 𝗧𝗔)
    (f : A ⟶ NumericalCoordinates.predicateObject C)
    (hf : ∀ x : NumericalTuples.Point A, D.val.Evalb (M := ℕ) ![(f.toFun x).val])
    (x : NumericalTuples.Point A) :
    ((wordCorestriction C D f hf).toFun x).val = (f.toFun x).val := rfl

private theorem wordCorestriction_injective {A : NumericalTuples.Object} (C D : PredicateCategory 𝗧𝗔)
    (f : A ⟶ NumericalCoordinates.predicateObject C)
    (hf : ∀ x : NumericalTuples.Point A, D.val.Evalb (M := ℕ) ![(f.toFun x).val])
    (hi : Function.Injective f.toFun) :
    Function.Injective (wordCorestriction C D f hf).toFun := by
  intro x y h
  apply hi
  apply Subtype.ext
  exact congrArg (fun z : NumericalTuples.Point (NumericalCoordinates.predicateObject D) => z.val) h

private theorem wordCorestriction_surjective {A : NumericalTuples.Object} (C D : PredicateCategory 𝗧𝗔)
    (f : A ⟶ NumericalCoordinates.predicateObject C)
    (hf : ∀ x : NumericalTuples.Point A, D.val.Evalb (M := ℕ) ![(f.toFun x).val])
    (hs : ∀ z : NumericalTuples.Point (NumericalCoordinates.predicateObject D),
      ∃ x : NumericalTuples.Point A, (f.toFun x).val = z.val) :
    Function.Surjective (wordCorestriction C D f hf).toFun := by
  intro z
  obtain ⟨x,hx⟩ := hs z
  exact ⟨x,Subtype.ext hx⟩

private theorem injective_of_mono {A B : NumericalTuples.Object} (f : A ⟶ B) [Mono f] :
    Function.Injective f.toFun :=
  (mono_iff_injective (NumericalUnderlying.functor.map f)).mp inferInstance

private theorem isIso_of_bijective {A B : NumericalTuples.Object} (f : A ⟶ B)
    (hi : Function.Injective f.toFun) (hs : Function.Surjective f.toFun) : IsIso f := by
  let _ : IsIso (NumericalUnderlying.functor.map f) := (isIso_iff_bijective _).mpr ⟨hi,hs⟩
  exact isIso_of_reflects_iso f NumericalUnderlying.functor

private theorem sentence_word_lift {A X : NumericalTuples.Object} (C D : PredicateCategory 𝗧𝗔)
    (j : X ⟶ A) (i : A ≅ NumericalCoordinates.predicateObject C) (fv : ℕ → ℕ)
    (hD : ∀ n : ℕ, D.val.Evalb ![n] ↔ C.val.Evalb ![n] ∧ fv n = 0)
    (hImage : ∀ a : NumericalTuples.Point A, (∃ x, j.toFun x = a) ↔ fv (i.hom.toFun a).val = 0) :
    ∀ z : NumericalTuples.Point (NumericalCoordinates.predicateObject D),
      ∃ x : NumericalTuples.Point X, (i.hom.toFun (j.toFun x)).val = z.val := by
  intro z
  let w : NumericalTuples.Point (NumericalCoordinates.predicateObject C) :=
    ⟨z.val,((hD z.val).mp z.property).1⟩
  let a : NumericalTuples.Point A := i.inv.toFun w
  have ha : i.hom.toFun a = w := congrArg (fun f => f.toFun w) i.inv_hom_id
  have hv : fv (i.hom.toFun a).val = 0 :=
    (congrArg fv (congrArg Subtype.val ha)).trans ((hD z.val).mp z.property).2
  obtain ⟨x,hx⟩ := (hImage a).mpr hv
  exact ⟨x,(congrArg (fun b => (i.hom.toFun b).val) hx).trans (congrArg Subtype.val ha)⟩

def literalSentence : numericalSyntax.sentenceObject ⟶ NumericalSentenceMorphisms.sentence :=
  wordCorestriction (A := numericalSyntax.sentenceObject)
    (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔)
    (ArithmeticLiteralModel.sentencePredicate : PredicateCategory 𝗧𝗔) formulaSentence closed

abbrev literalSentence_value (s : NumericalTuples.Point numericalSyntax.sentenceObject) :=
  wordCorestriction_value (A := numericalSyntax.sentenceObject)
    (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔)
    (ArithmeticLiteralModel.sentencePredicate : PredicateCategory 𝗧𝗔) formulaSentence closed s

private instance formulaSentence_mono : Mono formulaSentence := by
  dsimp only [formulaSentence]
  infer_instance

private abbrev literalSentence_injective :=
  wordCorestriction_injective (A := numericalSyntax.sentenceObject)
    (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔)
    (ArithmeticLiteralModel.sentencePredicate : PredicateCategory 𝗧𝗔)
    formulaSentence closed (injective_of_mono formulaSentence)

private abbrev originalFV : ℕ → ℕ :=
  ConcreteNamedSubstitution.freeVariables variableSymbols functionSymbols relationSymbols bound

private abbrev sentence_image_iff (a : NumericalTuples.Point numericalSyntax.algebra.a.2) :=
  (NumericalNamed.literal_sentence_iff NumericalNamed.variableObject functions relations bound a).trans
    (Iff.of_eq (congrArg (fun n : ℕ => n = 0)
      ((congrArg originalFV (formulaIso_value a)).trans
        (Algorithms.freeVariables_signature (M := ℕ) variableSymbols
          (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
          functionSymbols (LiteralSignature.coefficients functionSymbols)
          relationSymbols (LiteralSignature.coefficients relationSymbols) bound _)).symm))

private abbrev actual_sentence_word_lift :=
  sentence_word_lift (A := numericalSyntax.algebra.a.2) (X := numericalSyntax.sentenceObject)
    (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔)
    (ArithmeticLiteralModel.sentencePredicate : PredicateCategory 𝗧𝗔)
    numericalSyntax.sentenceInclusion formulaIso originalFV
    (fun n => ConcreteNamedComparison.literalSentenceCarrier_eval
      𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ n)
    (fun a => sentence_image_iff a)

private abbrev literalSentence_surjective :=
  wordCorestriction_surjective (A := numericalSyntax.sentenceObject)
    (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔)
    (ArithmeticLiteralModel.sentencePredicate : PredicateCategory 𝗧𝗔)
    formulaSentence closed actual_sentence_word_lift

instance literalSentence_isIso : IsIso literalSentence := by
  exact isIso_of_bijective literalSentence literalSentence_injective literalSentence_surjective

/-- The sentence comparison targets the proper PA sentence object. -/
def sentenceIso : numericalSyntax.sentenceObject ≅
    numericalInterpretation.obj originalSyntax.sentenceObject :=
  asIso literalSentence ≪≫ numericalInterpretation.mapIso ArithmeticLiteralModel.sentenceChart

/-- The square uses the actual formula chart and the actual PA inclusion. -/
theorem sentence_inclusion : sentenceIso.hom ≫ numericalInterpretation.map originalSyntax.sentenceInclusion =
    numericalSyntax.sentenceInclusion ≫ formulaIso.hom := by
  apply NumericalTuples.Map.ext
  funext s
  apply Subtype.ext
  change ((numericalInterpretation.map originalSyntax.sentenceInclusion).toFun
    ((numericalInterpretation.map ArithmeticLiteralModel.sentenceChart.hom).toFun
      (literalSentence.toFun s))).val = (formulaSentence.toFun s).val
  let w : PredicateInterpretation.Obj ℕ ArithmeticLiteralModel.sentencePredicate := literalSentence.toFun s
  have hj := numericalInterpretation_value
    (C := originalSyntax.sentenceObject) (D := originalSyntax.algebra.a.2)
    originalSyntax.sentenceInclusion
    ((numericalInterpretation.map ArithmeticLiteralModel.sentenceChart.hom).toFun w)
  have hc := numericalInterpretation_value
    (C := ArithmeticLiteralModel.sentencePredicate) (D := originalSyntax.sentenceObject)
    ArithmeticLiteralModel.sentenceChart.hom w
  exact (congrArg Subtype.val hj).trans
    ((congrArg (fun p : PredicateInterpretation.Obj ℕ originalSyntax.sentenceObject =>
      ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map originalSyntax.sentenceInclusion p).val) hc).trans
        ((ArithmeticLiteralModel.chart_value ℕ w).trans (literalSentence_value s)))

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Coordinates
