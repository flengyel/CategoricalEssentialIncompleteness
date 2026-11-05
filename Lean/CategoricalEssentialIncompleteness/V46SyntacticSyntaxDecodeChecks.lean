/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecode

/-! # Signature checks for actual syntax decode -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (P : PredicateCategory T) (a b : SyntaxPolynomial (PredicateCategory T))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (a.withParameters P) (b.withParameters P))) :
    SliceAlgebra T P B.a.1.left B.a.2.left a b := decode T P a b B

example (P : PredicateCategory T) (a b : SyntaxPolynomial (PredicateCategory T))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (a.withParameters P) (b.withParameters P)))
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p u : M)
    (h : (rawFiber P B.a.1.left B.a.2.left (chosenGraph T B.a.1.hom).graph
      (chosenGraph T B.a.2.hom).graph a).val.Evalb ![p, u]) :
    ∃! x : M, (decode T P a b B).termOp.val.Evalb ![p, u, x] :=
  (decode T P a b B).term_total_model p u h
