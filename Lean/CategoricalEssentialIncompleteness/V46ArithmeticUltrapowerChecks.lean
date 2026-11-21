/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUltrapower

/-! Arithmetic truth in the quotient, including unbounded quantifiers. -/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter
open CategoricalEssentialIncompleteness.V46

example {I : Type} (U : Ultrafilter I) (φ : ArithmeticSentence) :
    (ArithmeticUltrapower.Model U)↓[ℒₒᵣ] ⊧ φ ↔ ℕ↓[ℒₒᵣ] ⊧ φ :=
  ArithmeticUltrapower.sentence_iff U φ

example {I : Type} (U : Ultrafilter I) {n : ℕ} (φ : ArithmeticSemisentence n)
    (b : Fin n → I → ℕ) :
    φ.Evalb (M := ArithmeticUltrapower.Model U) (fun j => Germ.ofFun (b j)) ↔
      ∀ᶠ i in (U : Filter I), φ.Evalb (M := ℕ) (fun j => b j i) :=
  ArithmeticUltrapower.eval_representative U φ b

example {I : Type} (U : Ultrafilter I) :
    (ArithmeticUltrapower.Model U)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := inferInstance
