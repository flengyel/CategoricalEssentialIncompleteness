/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCoordinates

/-! # Signature checks for syntax coordinates -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (P C D : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).left)
    (hzp : (F T M).map ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).hom z = p) :
    ∃ u : M, (constantRepresentation T P C D a).val.Evalb ![p.val, u, z.val] :=
  constantRepresentation_cover T M P C D a p z hzp
