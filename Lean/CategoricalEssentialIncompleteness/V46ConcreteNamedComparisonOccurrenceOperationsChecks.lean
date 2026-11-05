/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOccurrenceOperations

/-! # Actual categorical operation values use the same named PA root code -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (u : M)
    (z : Obj T M ((SyntaxPolynomial.termExpression V σ d).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u,z.val]) :
    ((F T M).map (coprod.desc (lists T V).singleton ((lists T V).constructorOccurrences σ d)) z).val =
      ConcreteNamedSubstitution.freeVarsTermRoot σ d 0 u :=
  occurrenceTerm_operation_value T V M σ d u z hz
