/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedSentenceMorphism
public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedStandard
public import CategoricalEssentialIncompleteness.V46SyntacticOmegaRealization
public import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain

/-! The sentence morphism on the identity omega splitting. Its numerical
coordinates follow from its proved source graph in every PA model. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticLiteralTotal
open NamedArithmeticSignature

abbrev omegaPoint := SyntacticOmegaRealization.omegaPoint
abbrev omegaPoint_value := SyntacticOmegaRealization.omegaPoint_value

def literalPredicate : PredicateCategory 𝗣𝗔 :=
  ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound

def literalSentence : TotalSplit 𝗣𝗔 := (realization 𝗣𝗔).obj literalPredicate

def literalMorphism (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    GraphMorphism 𝗣𝗔 variableSymbols literalPredicate := NamedArithmeticFixedSubstitution.morphism φ hφ
def theta (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    @Quiver.Hom (TotalSplit 𝗣𝗔) inferInstance (ArithmeticOmegaComparison.identityOmega 𝗣𝗔) literalSentence :=
  SyntacticOmegaRealization.realizeFromOmega 𝗣𝗔 (C := literalPredicate) (literalMorphism φ hφ)

theorem canonical_graph (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M (ArithmeticOmegaComparison.identityOmega 𝗣𝗔))
    (y : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M literalSentence) :
    (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map (theta φ hφ) x = y ↔
      (NamedArithmeticFixedSubstitution.morphism φ hφ).graph.val.Evalb ![x.val.val,y.val.val] := by
  exact SyntacticOmegaRealization.realizeFromOmega_graph 𝗣𝗔 (C := literalPredicate)
    (literalMorphism φ hφ) M x y

theorem canonical_value (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M (ArithmeticOmegaComparison.identityOmega 𝗣𝗔)) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map (theta φ hφ) x).val.val =
      NamedArithmeticFixedSubstitution.value φ x.val.val := by
  have hg := (canonical_graph φ hφ M x
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map (theta φ hφ) x)).mp rfl
  exact (NamedArithmeticFixedSubstitution.morphism_graph_eval (M := M) φ hφ _ _).mp hg

theorem canonical_value_at (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map (theta φ hφ) (omegaPoint 𝗣𝗔 M n)).val.val =
      NamedArithmeticFixedSubstitution.value φ n := by
  rw [canonical_value,omegaPoint_value]

theorem standard_literal_result (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map (theta φ hφ) (omegaPoint 𝗣𝗔 ℕ n)).val.val =
        NamedArithmeticSignature.formulaCode out ∧ out.freeVariables = [] := by
  obtain ⟨out,hsub,hcode,hclosed⟩ := NamedArithmeticFixedSubstitution.standard_literal_result φ hφ n
  exact ⟨out,hsub,(canonical_value_at φ hφ ℕ n).trans hcode,hclosed⟩

end CategoricalEssentialIncompleteness.V46.NamedArithmeticLiteralTotal
