/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRepresentation

/-! # Signature checks for actual syntax representation -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (X Y : PredicateCategory T) (a : SyntaxPolynomial (PredicateCategory T)) :
    GraphMorphism T (a.eval.obj (X, Y)) (rawCarrier X Y a) :=
  encodePolynomial T X Y a

example (X Y : PredicateCategory T) (a : SyntaxPolynomial (PredicateCategory T))
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z : Obj T M (a.eval.obj (X, Y))) :
    ∃ u : M, (baseRepresentation T X Y a).val.Evalb ![u, z.val] :=
  baseRepresentation_cover T M X Y a z
