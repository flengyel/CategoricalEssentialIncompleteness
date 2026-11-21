/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonGraphs
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOccurrenceOperations
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # The numerical occurrence traversal is the categorical fold -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

/-- The numerical PA constructor equations commute with the categorical operations, on
every interpreted categorical source point. -/
theorem occurrencesPair_commutes :
    (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).map (occurrencesPair T V σ π d) ≫
      (categoricalSyntax T V σ π d).occurrenceAlgebra.str =
        (categoricalSyntax T V σ π d).algebra.str ≫ occurrencesPair T V σ π d := by
  apply Prod.ext
  · apply PredicateInterpretation.jointly_faithful T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    obtain ⟨u,hu⟩ := baseRepresentation_cover T M
      (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.termExpression V σ d) z
    have hp := (baseRepresentation_support T M
      (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.termExpression V σ d) u z.val hu).1
    have hm := representation_map T M
      (occurrencesArrow T V σ π d false) (occurrencesArrow T V σ π d true)
      (ConcreteNamedSubstitution.freeVariables V σ π d)
      (ConcreteNamedSubstitution.freeVariables V σ π d)
      (occurrencesArrow_value T V σ π d M false)
      (occurrencesArrow_value T V σ π d M true)
      (SyntaxPolynomial.termExpression V σ d) u z hu
    change ((F T M).map ((SyntaxPolynomial.termExpression V σ d).eval.map
      (occurrencesPair T V σ π d) ≫
        (categoricalSyntax T V σ π d).occurrenceAlgebra.str.1) z).val =
      ((F T M).map ((categoricalSyntax T V σ π d).algebra.str.1 ≫
        occurrencesArrow T V σ π d false) z).val
    rw [Functor.map_comp_apply,Functor.map_comp_apply]
    erw [occurrencesArrow_value T V σ π d M]
    have hs := postfixTerm_value T M (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) u z hu
    erw [hs,ConcreteNamedSubstitution.freeVariables_term_constructor V σ π d u hp]
    exact occurrenceTerm_operation_value T V M σ d _ _ hm
  · apply PredicateInterpretation.jointly_faithful T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    obtain ⟨u,hu⟩ := baseRepresentation_cover T M
      (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.formulaExpression V π d) z
    have hp := (baseRepresentation_support T M
      (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.formulaExpression V π d) u z.val hu).1
    have hm := representation_map T M
      (occurrencesArrow T V σ π d false) (occurrencesArrow T V σ π d true)
      (ConcreteNamedSubstitution.freeVariables V σ π d)
      (ConcreteNamedSubstitution.freeVariables V σ π d)
      (occurrencesArrow_value T V σ π d M false)
      (occurrencesArrow_value T V σ π d M true)
      (SyntaxPolynomial.formulaExpression V π d) u z hu
    change ((F T M).map ((SyntaxPolynomial.formulaExpression V π d).eval.map
      (occurrencesPair T V σ π d) ≫
        (categoricalSyntax T V σ π d).occurrenceAlgebra.str.2) z).val =
      ((F T M).map ((categoricalSyntax T V σ π d).algebra.str.2 ≫
        occurrencesArrow T V σ π d true) z).val
    rw [Functor.map_comp_apply,Functor.map_comp_apply]
    erw [occurrencesArrow_value T V σ π d M]
    have hs := postfixFormula_value T M (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) u z hu
    erw [hs,ConcreteNamedSubstitution.freeVariables_formula_constructor V σ π d u hp]
    exact occurrenceFormula_operation_value T V M π d _ _ hm

/-- This is an endofunctor-algebra morphism. Its commutation law is proved from the
numerical traversal and preserved finite geometry. -/
def occurrenceHom : (categoricalSyntax T V σ π d).algebra ⟶
    (categoricalSyntax T V σ π d).occurrenceAlgebra where
  f := occurrencesPair T V σ π d
  h := occurrencesPair_commutes T V σ π d

theorem occurrencesPair_eq_fold : occurrencesPair T V σ π d =
    (categoricalSyntax T V σ π d).fold (categoricalSyntax T V σ π d).occurrenceAlgebra :=
  (categoricalSyntax T V σ π d).fold_unique _ _ (occurrencesPair_commutes T V σ π d)

theorem termOccurrences_eq : (categoricalSyntax T V σ π d).termOccurrences =
    occurrencesArrow T V σ π d false :=
  (congrArg Prod.fst (occurrencesPair_eq_fold T V σ π d)).symm

theorem formulaOccurrences_eq : (categoricalSyntax T V σ π d).formulaOccurrences =
    occurrencesArrow T V σ π d true :=
  (congrArg Prod.snd (occurrencesPair_eq_fold T V σ π d)).symm

/-- Equality of the constructed quotient morphisms is a T-proof of equality with the
numerical graph, rather than only a statement about standard natural-number points. -/
theorem termOccurrences_graph_theory : Uniform T
    (chosenGraph T (categoricalSyntax T V σ π d).termOccurrences).graph
    (occurrencesGraph V σ π d false) := by
  apply (classOfGraph_eq_iff T
    (chosenGraph T (categoricalSyntax T V σ π d).termOccurrences)
    (occurrencesMorphism T V σ π d false)).mp
  change representedArrow T (chosenGraph T (categoricalSyntax T V σ π d).termOccurrences) =
    occurrencesArrow T V σ π d false
  exact (chosenGraph_class T _).trans (termOccurrences_eq T V σ π d)

theorem formulaOccurrences_graph_theory : Uniform T
    (chosenGraph T (categoricalSyntax T V σ π d).formulaOccurrences).graph
    (occurrencesGraph V σ π d true) := by
  apply (classOfGraph_eq_iff T
    (chosenGraph T (categoricalSyntax T V σ π d).formulaOccurrences)
    (occurrencesMorphism T V σ π d true)).mp
  change representedArrow T (chosenGraph T (categoricalSyntax T V σ π d).formulaOccurrences) =
    occurrencesArrow T V σ π d true
  exact (chosenGraph_class T _).trans (formulaOccurrences_eq T V σ π d)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem termOccurrences_value (word : Obj T M ((categoricalSyntax T V σ π d).algebra.a.1)) :
    ((F T M).map (categoricalSyntax T V σ π d).termOccurrences word).val =
      ConcreteNamedSubstitution.freeVariables V σ π d word.val := by
  rw [termOccurrences_eq]
  exact occurrencesArrow_value T V σ π d M false word

theorem formulaOccurrences_value (word : Obj T M ((categoricalSyntax T V σ π d).algebra.a.2)) :
    ((F T M).map (categoricalSyntax T V σ π d).formulaOccurrences word).val =
      ConcreteNamedSubstitution.freeVariables V σ π d word.val := by
  rw [formulaOccurrences_eq]
  exact occurrencesArrow_value T V σ π d M true word

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
