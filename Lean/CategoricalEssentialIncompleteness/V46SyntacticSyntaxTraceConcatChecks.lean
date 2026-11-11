/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTraceConcat


/-! # Statement checks in `V46SyntacticSyntaxTraceConcatChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.TraceConcatChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (p word suffix initial states other : M)
    (h : A.TraceRecord p word initial (len word) states)
    (g : A.TraceRecord p suffix (nth states (len word)) (len suffix) other) :
    ∃ combined : M,
      A.TraceRecord p (Words.append word suffix) initial (len (Words.append word suffix)) combined ∧
      nth combined (len (Words.append word suffix)) = nth other (len suffix) :=
  A.traceRecord_concat h g

example (p word initial states record new : M)
    (h : A.TraceRecord p word initial (len word) states)
    (hnew : A.valueStepGraph.val.Evalb ![p, record, nth states (len word), new]) :
    A.TraceRecord p (concat word record) initial (len (concat word record)) (concat states new) ∧
      nth (concat states new) (len (concat word record)) = new :=
  A.traceRecord_snoc h hnew
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.TraceConcatChecks
