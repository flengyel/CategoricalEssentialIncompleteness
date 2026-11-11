/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxHomGraphs

/-! # Explicit signature checks for HomGraphs -/

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

example [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] {P : PredicateCategory T}
    (a b : SyntaxPolynomial (PredicateCategory T))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (a.withParameters P) (b.withParameters P)))
    (f : constantFamily P (termCarrier a b) ⟶ B.a.1)
    (g : constantFamily P (formulaCarrier a b) ⟶ B.a.2)
    (h : (a.withParameters P).eval.map
      ((f,g) : (constantFamily P (termCarrier a b),
        constantFamily P (formulaCarrier a b)) ⟶ B.a) ≫ B.str.1 =
      (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.1 ≫ f)
    (p u x : M) (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (termCarrier a b) (formulaCarrier a b) a).val.Evalb ![u]) :
    (rawArrow T f).val.Evalb ![p,Coding.constructor false a u,x] ↔
      ∃ v : M, (mapRaw P (rawArrow T f) (rawArrow T g) a).val.Evalb ![p,u,v] ∧
        (decode T P a b B).termOp.val.Evalb ![p,v,x] :=
  candidateTermEquation T a b B f g M h p u x hp hu
