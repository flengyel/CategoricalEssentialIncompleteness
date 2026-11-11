/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSimulation


/-! # Statement checks in `V46SyntacticSyntaxSimulationChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SimulationChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (p word n states : M) (h : A.ValueRecord p word n states) :
    statusSort (runPrefix a b word n 1) = statusSort (nth states n) := A.valueRecord_sorts h

example (p word states : M) (formula : Bool) (h : A.ValueRecord p word (len word) states)
    (hw : (carrier formula a b).val.Evalb ![word]) :
    ∃ value : M, nth states (len word) = adjoin ⟪value, if formula then 1 else 0⟫ 0 + 1 :=
  A.valueRecord_singleton formula h hw
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SimulationChecks
