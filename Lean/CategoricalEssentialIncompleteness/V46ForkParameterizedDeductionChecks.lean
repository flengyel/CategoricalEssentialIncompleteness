/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkParameterizedDeduction

/-! # Independent complete-statement checks for Proposition 10.7 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.ForkParameterizedDeductionStatementChecks
open ForkFirstOrderFormula ForkParameterizedDeduction
variable (D P : Object)
local notation "S" => ForkCategoricalSyntax.categoricalSyntax D
local instance : Regular (Over P) := RegularSlices.regular P
local instance : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

example : CategoricalSyntax numbers (fun _ => ⊥_ Object) (fun _ => D) 0 := S
example : numbers ≅ (S).algebra.a.1 := ForkCategoricalSyntax.variableIso D
example : IsInitial (S).algebra := (S).initial
example : IsInitial (SyntaxPolynomial.algebraWithParameters
    (SyntaxPolynomial.termExpression numbers (fun _ => ⊥_ Object) 0)
    (SyntaxPolynomial.formulaExpression numbers (fun _ => D) 0) (S).algebra P) := (S).stable P
example : IsInitial ((S).lists.algebra.withParameters P).asAlgebra := (S).lists.stable P
example : IsPullback (prod.lift (𝟙 numbers) (𝟙 numbers)) (terminal.from numbers)
    (S).decidableVariables.test coprod.inr := (S).decidableVariables.diagonal

example : (S).sentenceObject = pullback (S).formulaOccurrences (S).lists.algebra.nil := rfl
example : IsPullback (S).admissibleInclusion (S).formulaSubstitution
    (S).formulaSubstitutionOption coprod.inr := (S).formulaSubstitution_isPullback
example {j k : WalkingSpan} (f : j ⟶ k) :
    (S).algebra.a.2.map f ≫ (S).formulaOccurrences.app k =
      (S).formulaOccurrences.app j ≫ (S).lists.algebra.carrier.map f :=
  (S).formulaOccurrences.naturality f
example {j k : WalkingSpan} (f : j ⟶ k) :
    ((S).algebra.a.2 ⨯ (S).substitutionParameters).map f ≫ (S).formulaSubstitutionOption.app k =
      (S).formulaSubstitutionOption.app j ≫ (OptionSyntax.obj (S).algebra.a.2).map f :=
  (S).formulaSubstitutionOption.naturality f

/-- All seven scheme parameter objects occur in order. The fourth and
seventh retain admissible-substitution pullbacks; the fifth retains absence. -/
example : (S).logicalParameters =
    ((((((((S).algebra.a.2 ⨯ (S).algebra.a.2) ⨿
      (((S).algebra.a.2 ⨯ (S).algebra.a.2) ⨯ (S).algebra.a.2)) ⨿
        ((S).algebra.a.2 ⨯ (S).algebra.a.2)) ⨿ (S).instantiationParameters) ⨿
          (S).distributionParameters) ⨿ (S).algebra.a.1) ⨿ (S).equalitySchemeParameters) := rfl
example : (S).logicalAxioms = coprod.desc (coprod.desc (coprod.desc (coprod.desc
    (coprod.desc (coprod.desc (S).hilbertOne (S).hilbertTwo) (S).hilbertThree)
      (S).hilbertInstantiation) (S).hilbertDistribution) (S).hilbertReflexivity)
        (S).hilbertEquality := rfl

example (A : Subobject (S).sentenceObject) :
    IsInitial (nullaryPresentations.proofs D A) := nullaryPresentations.initial D A
example (A : Subobject (S).sentenceObject) :
    ((S).logicalRules A.arrow).instances 0 = ((S).logicalParameters ⨿ (A : Object)) := rfl
example (A : Subobject (S).sentenceObject) :
    ((S).logicalRules A.arrow).instances 1 = (numbers ⨯ (S).algebra.a.2) := rfl
example (A : Subobject (S).sentenceObject) :
    ((S).logicalRules A.arrow).premises 1 = prod.snd := rfl
example (A : Subobject (S).sentenceObject) :
    ((S).logicalRules A.arrow).conclusion 1 = (S).quantifierConstructor := rfl
example (A : Subobject (S).sentenceObject) :
    ((S).logicalRules A.arrow).premises 2 = prod.lift prod.fst (S).implicationConstructor := rfl
example (A : Subobject (S).sentenceObject) :
    ((S).logicalRules A.arrow).conclusion 2 = prod.snd := rfl

example (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    IsInitial (proofs D P A) := initial D P A
example (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    (rules D P A.arrow).instances 0 =
      ((constantFamily P (S).logicalParameters) ⨿ (A : Over P)) := rfl
example (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    (rules D P A.arrow).premises 1 = prod.snd := rfl
example (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    (rules D P A.arrow).premises 2 = prod.lift prod.fst
      (FirstOrderRuleTransport.mappedImp (constantFamilyFunctor P) (S).implicationConstructor) := rfl

/-- Every axiom subobject of P × S is included, with its actual projection
to P. No constancy, recursive-membership or supplied initiality premise occurs. -/
example (A : Subobject (P ⨯ (S).sentenceObject)) :
    (axiomArrow D P A).left = A.arrow := rfl
example (A : Subobject (P ⨯ (S).sentenceObject)) : Mono (axiomArrow D P A) := inferInstance
example (A : Subobject (P ⨯ (S).sentenceObject)) :
    Σ B : Endofunctor.Algebra (printedRules D P A).inference, IsInitial B := printedStatement D P A

example (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference) :
    (printedFold D P A B).f.left ≫ B.a.hom = (printedAlgebra D P A).a.hom :=
  printedFold_conclusion D P A B
example (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference) :
    (printedRules D P A).inference.map (printedFold D P A B).f ≫ B.str =
      (printedAlgebra D P A).str ≫ (printedFold D P A B).f := printedFold_constructor D P A B
example (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference)
    (m : (printedAlgebra D P A).a.left ⟶ B.a.left)
    (hm : m ≫ B.a.hom = (printedAlgebra D P A).a.hom)
    (hc : (printedRules D P A).inference.map (Over.homMk m hm) ≫ B.str =
      (printedAlgebra D P A).str ≫ Over.homMk m hm) :
    m = (printedFold D P A B).f.left := printedFold_underlying_unique D P A B m hm hc
example (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference)
    {j k : WalkingSpan} (f : j ⟶ k) :
    (printedAlgebra D P A).a.left.map f ≫ (printedFold D P A B).f.left.app k =
      (printedFold D P A B).f.left.app j ≫ B.a.left.map f :=
  (printedFold D P A B).f.left.naturality f

/-- Both evaluation and the actual source constructor are compared by
an algebra isomorphism to the numerical finite-tree construction. -/
example (A : Subobject (P ⨯ (S).sentenceObject)) (j : WalkingSpan) :
    FiniteInferenceEvaluation.algebra (InitialRuleDiagrams.evaluation j) (printedRules D P A)
        (printedAlgebra D P A) ≅ NumericalDiagramDerivations.componentAlgebra (printedRules D P A) j :=
  NumericalDiagramDerivations.componentIso _ j

/-- Arbitrary presentations generate from their regular image, with no
initial-algebra assumption for the presentation morphism. -/
example (A : Over ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    ((presentationGeneration D P).obj A).val = generated D P (imageSubobject A.hom) :=
  presentationGeneration_obj D P A

#print axioms ForwardRuleRelabelling.input_identity
#print axioms ForwardRuleRelabelling.input_comp
#print axioms ForwardRuleRelabelling.comparison
#print axioms ForwardRuleRelabelling.fold_constructor
#print axioms ForwardRuleRelabelling.unique
#print axioms FiniteInferenceEvaluation.overIso
#print axioms FiniteInferenceEvaluation.comparison
#print axioms FiniteInferenceEvaluation.power_transformation
#print axioms FiniteInferenceEvaluation.branch_transformation
#print axioms FiniteInferenceEvaluation.sum_transformation
#print axioms FiniteInferenceEvaluation.algebra_transformation
#print axioms InitialRuleDiagrams.relabelling_id
#print axioms InitialRuleDiagrams.relabelling_comp
#print axioms InitialRuleDiagrams.transition_id
#print axioms InitialRuleDiagrams.transition_comp
#print axioms InitialRuleDiagrams.constructor_natural
#print axioms InitialRuleDiagrams.algebra
#print axioms InitialRuleDiagrams.sourceIso
#print axioms InitialRuleDiagrams.fold_natural
#print axioms InitialRuleDiagrams.fold_constructor
#print axioms InitialRuleDiagrams.initial
#print axioms NumericalDiagramDerivations.componentAlgebra_def
#print axioms NumericalDiagramDerivations.componentInitial
#print axioms NumericalDiagramDerivations.algebra
#print axioms NumericalDiagramDerivations.initial
#print axioms NumericalDiagramDerivations.componentIso
#print axioms NumericalDiagramDerivations.fold_underlying_unique
#print axioms NumericalDiagramDerivations.Parameterized.initial
#print axioms ForkParameterizedDeduction.nullaryPresentations
#print axioms ForkParameterizedDeduction.initial
#print axioms ForkParameterizedDeduction.printedRules
#print axioms ForkParameterizedDeduction.printedInitial
#print axioms ForkParameterizedDeduction.printedStatement
#print axioms ForkParameterizedDeduction.printedFold_constructor
#print axioms ForkParameterizedDeduction.printedFold_underlying_unique
#print axioms ForkParameterizedDeduction.presentationGeneration
#print axioms ForkParameterizedDeduction.presentationGeneration_obj
end CategoricalEssentialIncompleteness.V46.ForkParameterizedDeductionStatementChecks
