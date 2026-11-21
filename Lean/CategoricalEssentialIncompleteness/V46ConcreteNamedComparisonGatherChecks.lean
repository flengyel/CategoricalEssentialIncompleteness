/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonGather

/-! # Ordered argument concatenation computes the PA root function -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (V : PredicateCategory T)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (σ : ℕ → PredicateCategory T) (n : ℕ) (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors σ n).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.constructors σ n)).val.Evalb ![u,z.val]) :
    ((F T M).map ((lists T V).constructorOccurrences σ n) z).val =
      ConcreteNamedSubstitution.gather (SyntaxPolynomial.constructors σ n) u :=
  constructorOccurrences_value T V M σ n u z hz
