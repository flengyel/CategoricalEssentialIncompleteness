/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOperationLaws

/-! # Signature checks for syntax operationlaws -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (P : PredicateCategory T) (X : Over P × Over P)
    (a : SyntaxPolynomial (PredicateCategory T)) (Z : Over P)
    (f : (a.withParameters P).eval.obj X ⟶ Z) (p : Obj T M P) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj X).left) (v : Obj T M Z.left)
    (hz : (fiberRepresentation T P X a).val.Evalb ![p.val, u, z.val]) :
    (decodedOperation T X a f).val.Evalb ![p.val, u, v.val] ↔
      (F T M).map f.left z = v := decodedOperation_model T M X a f p u z v hz
