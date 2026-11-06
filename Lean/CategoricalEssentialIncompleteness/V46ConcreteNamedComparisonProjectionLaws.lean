/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPayloads

/-! # PA constructor equations for the two projected computations -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedProjectionLawsModelDecidableEq : DecidableEq M := Classical.decEq M

/-- The parameter may be arbitrary; no identity of the original
projection is assumed in these local constructor equations. -/
def originalComputation (x replacement word : M) : M :=
  ConcreteNamedSubstitution.original (ConcreteNamedSubstitution.substitutionPayload V σ π d x replacement word)

def occurrenceComputation (x replacement word : M) : M :=
  ConcreteNamedSubstitution.occurrences (ConcreteNamedSubstitution.substitutionPayload V σ π d x replacement word)

theorem originalComputation_term_constructor (x replacement u : M)
    (hu : (rawCarrier (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u]) :
    originalComputation V σ π d x replacement (Coding.constructor false (SyntaxPolynomial.termExpression V σ d) u) =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d)
        (ConcreteNamedSubstitution.mapChildren (originalComputation V σ π d x replacement)
          (originalComputation V σ π d x replacement) (SyntaxPolynomial.termExpression V σ d) u) := by
  unfold originalComputation
  rw [ConcreteNamedSubstitution.substitutionPayload_term_constructor V σ π d x replacement u hu,
    ConcreteNamedSubstitution.termRoot_original,ConcreteNamedSubstitution.mapChildren_comp]
  rfl

theorem originalComputation_formula_constructor (x replacement u : M)
    (hu : (rawCarrier (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![u]) :
    originalComputation V σ π d x replacement (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) u) =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (ConcreteNamedSubstitution.mapChildren (originalComputation V σ π d x replacement)
          (originalComputation V σ π d x replacement) (SyntaxPolynomial.formulaExpression V π d) u) := by
  unfold originalComputation
  rw [ConcreteNamedSubstitution.substitutionPayload_formula_constructor V σ π d x replacement u hu,
    ConcreteNamedSubstitution.formulaRoot_original,ConcreteNamedSubstitution.mapChildren_comp]
  rfl

theorem occurrenceComputation_term_constructor (x replacement u : M)
    (hu : (rawCarrier (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u]) :
    occurrenceComputation V σ π d x replacement (Coding.constructor false (SyntaxPolynomial.termExpression V σ d) u) =
      ConcreteNamedSubstitution.freeVarsTermRoot σ d 0
        (ConcreteNamedSubstitution.mapChildren (occurrenceComputation V σ π d x replacement)
          (occurrenceComputation V σ π d x replacement) (SyntaxPolynomial.termExpression V σ d) u) := by
  unfold occurrenceComputation
  rw [ConcreteNamedSubstitution.substitutionPayload_term_constructor V σ π d x replacement u hu,
    ConcreteNamedSubstitution.termRoot_occurrences,ConcreteNamedSubstitution.mapChildren_comp]
  rfl

theorem occurrenceComputation_formula_constructor (x replacement u : M)
    (hu : (rawCarrier (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![u]) :
    occurrenceComputation V σ π d x replacement (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) u) =
      ConcreteNamedSubstitution.freeVarsFormulaRoot π d 0
        (ConcreteNamedSubstitution.mapChildren (occurrenceComputation V σ π d x replacement)
          (occurrenceComputation V σ π d x replacement) (SyntaxPolynomial.formulaExpression V π d) u) := by
  unfold occurrenceComputation
  rw [ConcreteNamedSubstitution.substitutionPayload_formula_constructor V σ π d x replacement u hu,
    ConcreteNamedSubstitution.formulaRoot_occurrences,ConcreteNamedSubstitution.mapChildren_comp]
  rfl

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
