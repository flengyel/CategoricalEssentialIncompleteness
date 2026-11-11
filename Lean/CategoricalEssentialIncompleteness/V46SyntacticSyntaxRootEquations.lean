/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParser

/-! # Guarded constructor equations of ternary algebra-map graphs -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- These are precisely the constructor commutation equations of a
candidate algebra map. They impose neither an evaluator nor initiality. -/
def RootEquations (hT hF : TernaryGraph) : Prop :=
  (∀ p u value : M, P.val.Evalb ![p] →
    (rawCarrier (carrier false a b) (carrier true a b) a).val.Evalb ![u] →
      (hT.val.Evalb ![p, constructor false a u, value] ↔ ∃ v : M,
        (mapRaw P hT hF a).val.Evalb ![p, u, v] ∧ A.termOp.val.Evalb ![p, v, value])) ∧
  (∀ p u value : M, P.val.Evalb ![p] →
    (rawCarrier (carrier false a b) (carrier true a b) b).val.Evalb ![u] →
      (hF.val.Evalb ![p, constructor true b u, value] ↔ ∃ v : M,
        (mapRaw P hT hF b).val.Evalb ![p, u, v] ∧ A.formulaOp.val.Evalb ![p, v, value]))

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
