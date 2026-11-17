/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46NumericalDiagramDerivations
public import CategoricalEssentialIncompleteness.V46ForkCategoricalSyntax
public import CategoricalEssentialIncompleteness.V46FirstOrderRuleTransport
public import CategoricalEssentialIncompleteness.V46NullaryPresentationAdjunction
public import CategoricalEssentialIncompleteness.V46SubobjectImagePresentations

/-! # First-order fork deduction for axiom subobjects in every parameter slice -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkParameterizedDeduction
open ForkFirstOrderFormula

/-- Only axiom subobjects index the required initial proof algebras. -/
def nullaryPresentations : NullaryPresentations numbers where
  syntaxData := ForkCategoricalSyntax.categoricalSyntax
  proofs D A := NumericalDiagramDerivations.algebra
    ((ForkCategoricalSyntax.categoricalSyntax D).logicalRules A.arrow)
  initial D A := NumericalDiagramDerivations.initial
    ((ForkCategoricalSyntax.categoricalSyntax D).logicalRules A.arrow)

variable (D P : Object)
local notation "S" => ForkCategoricalSyntax.categoricalSyntax D
local instance : Regular (Over P) := RegularSlices.regular P
local instance : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

def rules {A : Over P} (axioms : A ⟶ (constantFamilyFunctor P).obj (S).sentenceObject) :=
  firstOrderRules ((constantFamilyFunctor P).map (S).logicalAxioms)
    ((constantFamilyFunctor P).map (S).sentenceInclusion) axioms
    (FirstOrderRuleTransport.mappedAll (constantFamilyFunctor P) (S).quantifierConstructor)
    (FirstOrderRuleTransport.mappedImp (constantFamilyFunctor P) (S).implicationConstructor)

def proofs (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    Endofunctor.Algebra (rules D P A.arrow).inference :=
  NumericalDiagramDerivations.Parameterized.algebra (rules D P A.arrow)

def initial (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    IsInitial (proofs D P A) := NumericalDiagramDerivations.Parameterized.initial (rules D P A.arrow)

def axiomArrow (A : Subobject (P ⨯ (S).sentenceObject)) :
    Over.mk (A.arrow ≫ (prod.fst : P ⨯ (S).sentenceObject ⟶ P)) ⟶
      (constantFamilyFunctor P).obj (S).sentenceObject := Over.homMk A.arrow rfl

instance axiomArrow_mono (A : Subobject (P ⨯ (S).sentenceObject)) : Mono (axiomArrow D P A) := by
  dsimp only [axiomArrow]
  infer_instance

/-- This is the inference endofunctor on the printed slice over P × Fm,
with the same parameter in all ordered premises and in their conclusion. -/
def printedRules (A : Subobject (P ⨯ (S).sentenceObject)) :
    RulePresentation (P ⨯ (S).algebra.a.2) 2 :=
  SliceRuleObjects.rules (rules D P (axiomArrow D P A))

def printedAlgebra (A : Subobject (P ⨯ (S).sentenceObject)) :
    Endofunctor.Algebra (printedRules D P A).inference :=
  NumericalDiagramDerivations.algebra (printedRules D P A)

def printedInitial (A : Subobject (P ⨯ (S).sentenceObject)) : IsInitial (printedAlgebra D P A) :=
  NumericalDiagramDerivations.initial (printedRules D P A)

def printedFold (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference) : printedAlgebra D P A ⟶ B :=
  (printedInitial D P A).to B

theorem printedFold_conclusion (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference) :
    (printedFold D P A B).f.left ≫ B.a.hom = (printedAlgebra D P A).a.hom := Over.w _

theorem printedFold_constructor (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference) :
    (printedRules D P A).inference.map (printedFold D P A B).f ≫ B.str =
      (printedAlgebra D P A).str ≫ (printedFold D P A B).f := (printedFold D P A B).h

theorem printedFold_underlying_unique (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules D P A).inference)
    (m : (printedAlgebra D P A).a.left ⟶ B.a.left)
    (hm : m ≫ B.a.hom = (printedAlgebra D P A).a.hom)
    (hc : (printedRules D P A).inference.map (Over.homMk m hm) ≫ B.str =
      (printedAlgebra D P A).str ≫ Over.homMk m hm) : m = (printedFold D P A B).f.left :=
  congrArg (fun n => n.f.left)
    ((printedInitial D P A).hom_ext (⟨Over.homMk m hm, hc⟩ : printedAlgebra D P A ⟶ B) _)

/-- The every-parameter finite-derivation clause has no supplied
initiality, evaluator or transition-compatibility hypothesis. -/
def printedStatement (A : Subobject (P ⨯ (S).sentenceObject)) :
    Σ B : Endofunctor.Algebra (printedRules D P A).inference, IsInitial B :=
  ⟨printedAlgebra D P A, printedInitial D P A⟩

def generated (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :=
  FirstOrderReflection.generated (proofs D P) A

/-- Arbitrary axiom morphisms enter generation through their regular
images. Only the subobject-indexed proof family is used. -/
def presentationGeneration := FirstOrderReflection.presentationGeneration (proofs D P) (initial D P)

theorem presentationGeneration_obj
    (A : Over ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    ((presentationGeneration D P).obj A).val = generated D P (imageSubobject A.hom) := rfl

end CategoricalEssentialIncompleteness.V46.ForkParameterizedDeduction
