/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkCategoricalSyntax

/-! # Independent checks of the full fork syntax and substitution interface

These statements cover the syntax clauses of Proposition 10.7. Initial
finite derivation algebras remain a separate obligation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.ForkCategoricalSyntaxStatementChecks
open ForkFirstOrderFormula ForkCategoricalSyntax
variable (D P : Object)
local notation "S" => categoricalSyntax D
local notation "K" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression numbers (fun _ => ⊥_ Object) 0)
  (SyntaxPolynomial.formulaExpression numbers (fun _ => D) 0)
local notation "KP" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.withParameters P (SyntaxPolynomial.termExpression numbers (fun _ => ⊥_ Object) 0))
  (SyntaxPolynomial.withParameters P (SyntaxPolynomial.formulaExpression numbers (fun _ => D) 0))

example : CategoricalSyntax numbers (fun _ => ⊥_ Object) (fun _ => D) 0 := S
example : IsInitial (S).algebra := (S).initial
example : IsInitial (SyntaxPolynomial.algebraWithParameters
    (SyntaxPolynomial.termExpression numbers (fun _ => ⊥_ Object) 0)
    (SyntaxPolynomial.formulaExpression numbers (fun _ => D) 0) (S).algebra P) := (S).stable P

example (T F : Object) : (K).obj (T, F) =
    (numbers ⨿ ((⊥_ Object) ⨯ (⊤_ Object)),
      (((((T ⨯ T) ⨿ (D ⨯ (⊤_ Object))) ⨿ F) ⨿ (F ⨯ F)) ⨿ (numbers ⨯ F))) := rfl

example : numbers ≅ (S).algebra.a.1 := variableIso D
example : (variableIso D).hom = (S).variableConstructor := rfl
example {j k : WalkingSpan} (f : j ⟶ k) : numbers.map f = 𝟙 _ := rfl
example : IsPullback (prod.lift (𝟙 numbers) (𝟙 numbers)) (terminal.from numbers)
    (S).decidableVariables.test coprod.inr := (S).decidableVariables.diagonal

/-- The target is every algebra over P, with no constant-family restriction. -/
example (B : Endofunctor.Algebra KP) :
    (KP).map ((S).foldWithParameters P B) ≫ B.str =
      (SyntaxPolynomial.algebraWithParameters
        (SyntaxPolynomial.termExpression numbers (fun _ => ⊥_ Object) 0)
        (SyntaxPolynomial.formulaExpression numbers (fun _ => D) 0) (S).algebra P).str ≫
          (S).foldWithParameters P B := (S).foldWithParameters_commutes P B

/-- Uniqueness quantifies over every pair of natural underlying morphisms. -/
example (B : Endofunctor.Algebra KP)
    (m : (constantFamily P (S).algebra.a.1, constantFamily P (S).algebra.a.2) ⟶ B.a)
    (hm : (KP).map m ≫ B.str = (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression numbers (fun _ => ⊥_ Object) 0)
      (SyntaxPolynomial.formulaExpression numbers (fun _ => D) 0) (S).algebra P).str ≫ m) :
    m = (S).foldWithParameters P B := (S).foldWithParameters_unique P B m hm

example (B : Endofunctor.Algebra KP) :
    ((S).foldWithParameters P B).1.left ≫ B.a.1.hom =
      (constantFamily P (S).algebra.a.1).hom := Over.w _
example (B : Endofunctor.Algebra KP) :
    ((S).foldWithParameters P B).2.left ≫ B.a.2.hom =
      (constantFamily P (S).algebra.a.2).hom := Over.w _

example : IsInitial (S).lists.algebra.asAlgebra := (S).lists.initial
example : IsInitial ((S).lists.algebra.withParameters P).asAlgebra := (S).lists.stable P
example (B : ListAlgebra (constantFamily P numbers)) :
    ((S).lists.algebra.withParameters P).nil ≫ (S).lists.foldWithParameters P B = B.nil :=
  (S).lists.foldWithParameters_nil P B
example (B : ListAlgebra (constantFamily P numbers)) :
    ((S).lists.algebra.withParameters P).cons ≫ (S).lists.foldWithParameters P B =
      prod.map (𝟙 _) ((S).lists.foldWithParameters P B) ≫ B.cons :=
  (S).lists.foldWithParameters_cons P B
example (B : ListAlgebra (constantFamily P numbers))
    (m : constantFamily P (S).lists.algebra.carrier ⟶ B.carrier)
    (hnil : ((S).lists.algebra.withParameters P).nil ≫ m = B.nil)
    (hcons : ((S).lists.algebra.withParameters P).cons ≫ m = prod.map (𝟙 _) m ≫ B.cons) :
    m = (S).lists.foldWithParameters P B := (S).lists.foldWithParameters_unique P B m hnil hcons

example : (S).algebra.a.1 ⟶ (S).lists.algebra.carrier := termOccurrences D
example : (S).algebra.a.2 ⟶ (S).lists.algebra.carrier := formulaOccurrences D
example {j k : WalkingSpan} (f : j ⟶ k) :
    (formulas D).map f ≫ (formulaOccurrences D).app k =
      (formulaOccurrences D).app j ≫ (lists D).map f := occurrences_natural D f
example : sentences D = pullback (formulaOccurrences D) (S).lists.algebra.nil := rfl
example : Mono (sentenceInclusion D) := inferInstance
example : IsPullback (sentenceInclusion D)
    (pullback.snd (formulaOccurrences D) (S).lists.algebra.nil)
    (formulaOccurrences D) (S).lists.algebra.nil := sentence_pullback D

example : (terms D) ⨯ (numbers ⨯ terms D) ⟶ terms D := termSubstitution D
example : (formulas D) ⨯ (numbers ⨯ terms D) ⟶ (⊤_ Object) ⨿ formulas D :=
  formulaSubstitutionOption D
example {j k : WalkingSpan} (f : j ⟶ k) :
    ((formulas D) ⨯ (S).substitutionParameters).map f ≫ (formulaSubstitutionOption D).app k =
      (formulaSubstitutionOption D).app j ≫ (OptionSyntax.obj (formulas D)).map f :=
  substitution_natural D f
example : Mono (admissibleInclusion D) := inferInstance
example : IsPullback (admissibleInclusion D) (formulaSubstitution D)
    (formulaSubstitutionOption D) coprod.inr := substitution_pullback D
example : IsCompl (Subobject.mk (admissibleInclusion D))
    (Subobject.mk (pullback.fst (formulaSubstitutionOption D) coprod.inl)) :=
  (S).admissibility_complemented
example : (S).substitutionFold ≫ (S).substitutionOriginalHom.f =
    𝟙 (constantFamily (S).substitutionParameters (terms D),
      constantFamily (S).substitutionParameters (formulas D)) := substitution_original D

#print axioms NumericalDiagramSyntax.componentAlgebra_def
#print axioms NumericalDiagramSyntax.componentInitial
#print axioms NumericalDiagramSyntax.componentStable
#print axioms ProductAdjunction.square
#print axioms SliceAlgebraInitiality.comparison
#print axioms SliceAlgebraInitiality.transition_constructor
#print axioms SliceAlgebraInitiality.fold_natural
#print axioms SliceAlgebraInitiality.foldMap
#print axioms SliceAlgebraInitiality.fold_constructor
#print axioms SliceAlgebraInitiality.initial
#print axioms LabelledParameterAlgebras.comparison_data
#print axioms LabelledParameterAlgebras.algebra_data
#print axioms LabelledParameterAlgebras.toInitial
#print axioms LabelledParameterAlgebras.fromInitial
#print axioms DiagramParameterConstructor.square
#print axioms NumericalDiagramParameterStability.constructor_square
#print axioms NumericalDiagramParameterStability.sourceIso
#print axioms NumericalDiagramParameterStability.componentInitial
#print axioms NumericalDiagramParameterStability.labelledInitial
#print axioms NumericalDiagramParameterStability.stable
#print axioms NumericalDiagramParameterStability.data
#print axioms ListAlgebraProjection.constructor_eq
#print axioms ListAlgebraProjection.initial
#print axioms ListAlgebraProjection.parameter_nil
#print axioms ListAlgebraProjection.parameter_cons
#print axioms ListAlgebraProjection.parameterIso
#print axioms DiagramStableLists.stableListAlgebra
#print axioms ForkCategoricalSyntax.categoricalSyntax
#print axioms ForkCategoricalSyntax.variableIso
#print axioms ForkCategoricalSyntax.occurrences_natural
#print axioms ForkCategoricalSyntax.substitution_natural
#print axioms ForkCategoricalSyntax.sentence_pullback
#print axioms ForkCategoricalSyntax.substitution_pullback
#print axioms ForkCategoricalSyntax.substitution_original
end CategoricalEssentialIncompleteness.V46.ForkCategoricalSyntaxStatementChecks
