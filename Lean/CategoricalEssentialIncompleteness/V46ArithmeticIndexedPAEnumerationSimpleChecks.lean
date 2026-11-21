/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationSimple


/-! # The Σ₁ enumeration of the finite arithmetic/order schemes -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.SimpleChecks
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

example (out : ℕ) :
    simpleCarrier.val.Evalb ![out] ↔ ∃ k : Fin 17, ∃ environment : ℕ,
      (k.val = 3 →
        Words.value (.slot 2) environment ≠ Words.value (.slot 0) environment ∧
        Words.value (.slot 2) environment ≠ Words.value (.slot 1) environment) ∧
      out = formulaCode ((simpleTemplate k).instantiate environment) :=
  simpleCarrier_standard out

example (out : ℕ) (h : simpleCarrier.val.Evalb ![out]) :
    ∃ φ : Formula, PASeed φ ∧ formulaCode φ = out := simpleCarrier_seed out h

example {φ : Formula} (h : PASeed φ) :
    (∃ k : Fin 17, ∃ environment : ℕ, fresh k environment ∧
      (simpleTemplate k).instantiate environment = φ) ∨
    ∃ x body base step, φ = inductionMatrix x body base step ∧
      body.FreeFor x NamedArithmeticSignature.zero ∧
      body.FreeFor x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) ∧
      body.substitute x NamedArithmeticSignature.zero = some base ∧
      body.substitute x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) = some step :=
  seed_cases h

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.SimpleChecks
