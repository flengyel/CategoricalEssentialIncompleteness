/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTrace


/-! # Statement checks in `V46SyntacticSyntaxTraceChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.TraceChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (p word n states i : M) (h : A.ValueRecord p word n states)
    (hi : i ≤ n) (hz : nth states i = 0) : nth states n = 0 :=
  SliceAlgebra.ValueRecord.error_suffix A h hi hz

example (p word n states tail : M) (h : A.ValueRecord p word n states)
    (hend : nth states n ≠ 0)
    (ht : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, tail]) :
    A.TraceRecord p word (tail + 1) n (frameVector states tail) :=
  A.valueRecord_frame h hend ht
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.TraceChecks
