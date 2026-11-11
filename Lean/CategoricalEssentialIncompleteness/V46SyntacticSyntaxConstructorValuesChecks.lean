/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorValues

/-! # Explicit signature checks for ConstructorValues -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example (P X Y Z : PredicateCategory T) (a : SyntaxPolynomial (PredicateCategory T))
    (f : a.eval.obj (X,Y) ⟶ Z) :
    (SyntaxPolynomial.parameterComparison P (X,Y) a ≫
      (constantFamilyFunctor P).map f).left ≫ prod.snd =
        parameterValueMap T P X Y a ≫ f := parameterOperation_snd T P X Y Z a f
