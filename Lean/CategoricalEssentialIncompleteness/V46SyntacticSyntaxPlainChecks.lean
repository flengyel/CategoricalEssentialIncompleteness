/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Exact plain-parser-carrier initiality checks -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (a b : SyntaxPolynomial (PredicateCategory T)) :
    (plainPostfixAlgebra T a b).a.1 = (Postfix.plainCarrier false a b : PredicateCategory T) := rfl

example (a b : SyntaxPolynomial (PredicateCategory T)) (P : PredicateCategory T) :
    IsInitial (SyntaxPolynomial.algebraWithParameters a b (plainPostfixAlgebra T a b) P) :=
  plainWithParametersInitial T a b P

example (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) :
    CategoricalSyntax V σ π d := plainCategoricalSyntax T V σ π d

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (formula : Bool) (a b : RawPolynomial) (u : M)
    (hu : (rawCarrier (Postfix.plainCarrier false a b) (Postfix.plainCarrier true a b)
      (if formula then b else a)).val.Evalb ![u]) :
    (Postfix.toPlainMorphism T formula a b).graph.val.Evalb
      ![Coding.constructor formula (if formula then b else a) u,
        Coding.constructor formula (if formula then b else a) u] :=
  Postfix.toPlain_constructor_graph T formula a b u hu
