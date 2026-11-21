/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFibers

/-! # Signature checks for syntax fibers -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (P : PredicateCategory T) (X : Over P × Over P)
    (a : SyntaxPolynomial (PredicateCategory T))
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p : Obj T M P) (u : M)
    (h : (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
      (chosenGraph T X.2.hom).graph a).val.Evalb ![p.val, u]) :
    ∃! z : Obj T M ((a.withParameters P).eval.obj X).left,
      (fiberRepresentation T P X a).val.Evalb ![p.val, u, z.val] :=
  fiberRepresentation_existsUnique T M P X a p u h
