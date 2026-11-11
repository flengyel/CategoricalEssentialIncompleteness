/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationWords


/-! # Statement checks in `V46ArithmeticIndexedPAEnumerationWordsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.WordsChecks
open NamedArithmeticSignature ArithmeticIndexedPAEnumeration

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (expression : Words.Expr) (out environment : M) :
    (Words.graph expression).val.Evalb ![out,environment] ↔
      out = Words.value expression environment := Words.graph_eval expression out environment

example (name body : Words.Expr) (environment x : ℕ) (φ : Formula)
    (hx : Words.value name environment = x)
    (hφ : Words.value body environment = formulaCode φ) :
    Words.value (Words.all name body) environment = formulaCode (.all x φ) :=
  Words.all_value name body environment x φ hx hφ

example (name body base step : Words.Expr) (environment x : ℕ)
    (φ φ0 φs : Formula) (hx : Words.value name environment = x)
    (hφ : Words.value body environment = formulaCode φ)
    (h0 : Words.value base environment = formulaCode φ0)
    (hs : Words.value step environment = formulaCode φs) :
    Words.value (Words.inductionMatrix name body base step) environment =
      formulaCode (.imp φ0 (.imp (.all x (.imp φ φs)) (.all x φ))) :=
  Words.inductionMatrix_value name body base step environment x φ φ0 φs hx hφ h0 hs

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.WordsChecks
