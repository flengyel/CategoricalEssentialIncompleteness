/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationInduction


/-! # Statement checks in `V46ArithmeticIndexedPAEnumerationInductionChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.InductionChecks
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

example (out : ℕ) :
    seedCarrier.val.Evalb ![out] ↔ ∃ ψ : Formula, PASeed ψ ∧ formulaCode ψ = out :=
  seedCarrier_standard out

example (x : ℕ) (φ φ0 φs : Formula)
    (h0 : φ.FreeFor x NamedArithmeticSignature.zero)
    (hs : φ.FreeFor x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one))
    (s0 : φ.substitute x NamedArithmeticSignature.zero = some φ0)
    (ss : φ.substitute x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) = some φs) :
    inductionCarrier.val.Evalb
      ![formulaCode (.imp φ0 (.imp (.all x (.imp φ φs)) (.all x φ)))] :=
  inductionCarrier_of_native ⟨x,φ,φ0,φs,rfl,h0,hs,s0,ss⟩

example (out : ℕ) (h : inductionCarrier.val.Evalb ![out]) :
    ∃ ψ : Formula, PASeed ψ ∧ formulaCode ψ = out := inductionCarrier_seed out h

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.InductionChecks
