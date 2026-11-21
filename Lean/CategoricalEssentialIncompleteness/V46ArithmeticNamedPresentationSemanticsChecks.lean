/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationSemantics


/-! # Semantic roundtrip for each named arithmetic sentence -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature
universe w
example {K : Type w} [ORingStructure K] (n : ℕ) (φ : Formula) (hφ : Bound n φ) (ρ : ℕ → K) :
    (formula n φ).Eval (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) ↔
      φ.Holds ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations ρ :=
  formula_semantics n φ hφ ρ
example {K : Type w} [ORingStructure K] (φ : Formula) (hφ : φ.freeVariables = []) (ρ : ℕ → K) :
    (sentence φ hφ).Evalb (s := Arithmetic.standardModel K) ![] ↔
      φ.Holds ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations ρ :=
  sentence_semantics φ hφ ρ
end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
