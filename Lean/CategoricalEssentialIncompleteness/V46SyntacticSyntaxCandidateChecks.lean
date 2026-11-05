/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCandidate

/-! # Signature checks for syntax candidate -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example (P C : PredicateCategory T) (X : Over P)
    (f : constantFamily P C ⟶ X) (p : Obj T M P) (u : Obj T M C) :
    ∃! v : Obj T M X.left, (rawArrow T f).val.Evalb ![p.val, u.val, v.val] :=
  rawArrow_existsUnique T M f p u

example (P C : PredicateCategory T) (X : Over P)
    (f : constantFamily P C ⟶ X) (p : Obj T M P) (u : Obj T M C)
    (z : Obj T M (P ⨯ C)) (v : Obj T M X.left)
    (hz : (constantLeaf T P C).val.Evalb ![p.val, u.val, z.val]) :
    (rawArrow T f).val.Evalb ![p.val, u.val, v.val] ↔ (F T M).map f.left z = v :=
  rawArrow_model T M f p u z v hz
