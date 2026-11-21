/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxUniqueness
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorLaws


/-! # Numerical node-count comparison from constructor equations -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.UniquenessChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

example (hT hF : TernaryGraph) (hroot : A.RootEquations (M := M) hT hF)
    (formula : Bool) (p word x y : M)
    (hx : (if formula then hF else hT).val.Evalb ![p, word, x])
    (hy : (A.evaluationFormula formula).val.Evalb ![p, word, y]) : x = y :=
  A.comparison_of_root_equations hT hF hroot A.evaluation_root_equations formula p word x y hx hy
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.UniquenessChecks
