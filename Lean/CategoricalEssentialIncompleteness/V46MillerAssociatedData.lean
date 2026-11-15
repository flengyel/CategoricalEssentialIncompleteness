/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerCanonicalAxiomIncompleteness
public import CategoricalEssentialIncompleteness.V46MillerParameterizedDeduction
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemePoints
public import CategoricalEssentialIncompleteness.V46NullaryLogicalPoint

/-! # The actual Miller field theory and its common logical point -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.AssociatedData
variable (a : Point)
local notation "Ω" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S₁" => NamedProofImage.syntaxData (Ω) (σ) (π) (d)

def syntaxData := NamedSyntaxComparison.canonicalPresentedSyntax a (V) (σ) (π) (d)

/-- Only axiom subobjects index the proof family. -/
def proofs (A : Subobject (syntaxData a).sentenceObject) :
    Endofunctor.Algebra ((syntaxData a).logicalRules A.arrow).inference :=
  CanonicalAxiomIncompleteness.proofAlgebra a A.arrow

def initial (A : Subobject (syntaxData a).sentenceObject) : IsInitial (proofs a A) :=
  CanonicalAxiomIncompleteness.proofInitial a A.arrow

abbrev Theory := FirstOrderReflection.Theory (proofs a)

/-- The printed t_a is the actual generated sentence-conclusion image. -/
def base : Subobject (syntaxData a).sentenceObject :=
  imageSubobject (CanonicalPresentation.chosenSentenceConclusion a (σ) (π) (d)
    (RealClosedAxioms.theoryAxioms a) (RealClosedAxioms.theoryAxioms_enumerable a))

def pointDomain : Total.CanonicalTotal a :=
  (E).functor.obj (⟨Total.terminalCarrier⟩ : Total.TotalCategory (Ω))

def pointDomain_terminal : IsTerminal (pointDomain a) :=
  IsTerminal.isTerminalObj (E).functor _ (Total.terminalIsTerminal (P := (Ω)))

section UniformPoints
variable {Ω' : Uniform.Family} {X Y : Total.TotalCategory Ω'}
theorem point_natural (f : X ⟶ Y) (x : Total.underlying.obj X) :
    Total.underlyingPoint (Total.underlying.map f x) = Total.underlyingPoint x ≫ f := by
  exact ConcreteCategory.congr_hom
    ((Total.underlyingHomComparison (P := Ω')).hom.naturality f) x
end UniformPoints

theorem zero_equality_closed :
    (NamedFiniteSyntax.Formula.equal OrderedFieldSyntax.zero OrderedFieldSyntax.zero :
      OrderedFieldSyntax.Formula).freeVariables =
      [] := by simp [NamedFiniteSyntax.Formula.freeVariables]

def sourcePoint : (⟨Total.terminalCarrier⟩ : Total.TotalCategory (Ω)) ⟶ (S₁).sentenceObject :=
  Total.underlyingPoint (NamedProofImage.sentencePoint (Ω) (σ) (π) (d)
    (.equal OrderedFieldSyntax.zero OrderedFieldSyntax.zero) zero_equality_closed)

def sourceLogical : (⟨Total.terminalCarrier⟩ : Total.TotalCategory (Ω)) ⟶ (S₁).logicalParameters :=
  Total.underlyingPoint (NamedProofImage.termPoint (Ω) (σ) (π) (d) OrderedFieldSyntax.zero) ≫
    coprod.inr ≫ coprod.inl

theorem sourceDiagram : sourceLogical a ≫ (S₁).logicalAxioms =
    sourcePoint a ≫ (S₁).sentenceInclusion := by
  dsimp only [sourceLogical, sourcePoint]
  simp only [CategoricalSyntax.logicalAxioms, Category.assoc, coprod.inl_desc, coprod.inr_desc]
  rw [← point_natural, ← point_natural,
    NamedProofImage.Points.hilbertReflexivity_point, NamedProofImage.sentencePoint_inclusion]

def theoremPoint : pointDomain a ⟶ (syntaxData a).sentenceObject :=
  (E).functor.map (sourcePoint a) ≫ (CanonicalPresentation.mappedSentenceIso a (V) (σ) (π) (d)).hom

def logicalPoint : pointDomain a ⟶ (syntaxData a).logicalParameters :=
  (E).functor.map (sourceLogical a) ≫
    (CanonicalPresentation.logicalParametersIso a (V) (σ) (π) (d)).hom

set_option maxHeartbeats 0 in
theorem logicalPoint_diagram : logicalPoint a ≫ (syntaxData a).logicalAxioms =
    theoremPoint a ≫ (syntaxData a).sentenceInclusion := by
  dsimp only [logicalPoint, theoremPoint]
  erw [Category.assoc, ← CanonicalPresentation.logicalAxioms_comparison a (V) (σ) (π) (d),
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, sourceDiagram,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc,
    CanonicalPresentation.mappedSentenceIso_inclusion a (V) (σ) (π) (d)]

/-- The same closed theorem 0 = 0 factors through every closed theory,
without a consistency or a constant-family assumption. -/
theorem point_factors (U : Theory a) :
    ∃ p : pointDomain a ⟶ (U.val : Total.CanonicalTotal a), p ≫ U.val.arrow = theoremPoint a :=
  NullaryLogicalPoint.factors (syntaxData a).logicalAxioms (syntaxData a).sentenceInclusion
    (syntaxData a).quantifierConstructor (syntaxData a).implicationConstructor (proofs a)
    (theoremPoint a) (logicalPoint a) (logicalPoint_diagram a) U

def point (U : Theory a) : pointDomain a ⟶ (U.val : Total.CanonicalTotal a) :=
  (point_factors a U).choose

end CategoricalEssentialIncompleteness.V46.Miller.AssociatedData
