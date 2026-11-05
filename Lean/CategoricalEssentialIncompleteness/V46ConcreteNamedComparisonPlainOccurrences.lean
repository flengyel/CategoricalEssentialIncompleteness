/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOccurrences

/-! # The plain parser presentation has the same numerical free-variable fold -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The actual inverse quotient arrow changes only the displayed
predicate and fixes every word in every T-model. -/
theorem plainCarrierIso_inv_value (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (formula : Bool) (a b : RawPolynomial) (word : Obj T M (Postfix.plainCarrier formula a b)) :
    ((F T M).map (Postfix.plainCarrierIso T formula a b).inv word).val = word.val := by
  let out := (F T M).map (Postfix.plainCarrierIso T formula a b).inv word
  have h := (PredicateInterpretation.map_class_eq_iff T M
    (Postfix.fromPlainMorphism T formula a b) word out).mp rfl
  exact ((GraphMorphism.identityGraph_eval _ word.val out.val).mp h).2

variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

/-- The constructor-preserving plain algebra isomorphism transports the
actual occurrence Hom, not a separately assumed evaluator. -/
def plainOccurrenceHom : (plainCategoricalSyntax T V σ π d).algebra ⟶
    (plainCategoricalSyntax T V σ π d).occurrenceAlgebra :=
  (plainAlgebraIso T (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)).inv ≫ occurrenceHom T V σ π d

theorem plain_termOccurrences_eq : (plainCategoricalSyntax T V σ π d).termOccurrences =
    (Postfix.plainCarrierIso T false (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).inv ≫ occurrencesArrow T V σ π d false := by
  have h := (plainCategoricalSyntax T V σ π d).fold_unique
    (plainCategoricalSyntax T V σ π d).occurrenceAlgebra
    (plainOccurrenceHom T V σ π d).f (plainOccurrenceHom T V σ π d).h
  exact (congrArg Prod.fst h).symm

theorem plain_formulaOccurrences_eq : (plainCategoricalSyntax T V σ π d).formulaOccurrences =
    (Postfix.plainCarrierIso T true (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).inv ≫ occurrencesArrow T V σ π d true := by
  have h := (plainCategoricalSyntax T V σ π d).fold_unique
    (plainCategoricalSyntax T V σ π d).occurrenceAlgebra
    (plainOccurrenceHom T V σ π d).f (plainOccurrenceHom T V σ π d).h
  exact (congrArg Prod.snd h).symm

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem plain_termOccurrences_value
    (word : Obj T M ((plainCategoricalSyntax T V σ π d).algebra.a.1)) :
    ((F T M).map (plainCategoricalSyntax T V σ π d).termOccurrences word).val =
      ConcreteNamedSubstitution.freeVariables V σ π d word.val := by
  rw [plain_termOccurrences_eq,Functor.map_comp_apply]
  erw [occurrencesArrow_value T V σ π d M,plainCarrierIso_inv_value T M]

theorem plain_formulaOccurrences_value
    (word : Obj T M ((plainCategoricalSyntax T V σ π d).algebra.a.2)) :
    ((F T M).map (plainCategoricalSyntax T V σ π d).formulaOccurrences word).val =
      ConcreteNamedSubstitution.freeVariables V σ π d word.val := by
  rw [plain_formulaOccurrences_eq,Functor.map_comp_apply]
  erw [occurrencesArrow_value T V σ π d M,plainCarrierIso_inv_value T M]

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
