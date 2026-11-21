/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationAlpha


/-! # Original-name quantifiers and computed alpha comparison -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature
example {ξ : Type} (φ : Semiformula ℒₒᵣ ξ 1) (seed x y : ℕ) (fn : ξ → ℕ)
    (hx : x < seed) (hy : y < seed) (hf : ∀ i, fn i ≠ x) :
    (ArithmeticNamedOpenTranslation.formula seed ![x] fn φ).substitute x (.var y) =
      some (ArithmeticNamedOpenTranslation.formula seed ![y] fn φ) :=
  body_rename φ seed x y fn hx hy hf
example (A : SyntacticPredicates.Carrier) {ξ : Type} (φ : Semiformula ℒₒᵣ ξ 1)
    (seed x y : ℕ) (fn : ξ → ℕ) (hx : x < seed) (hy : y < seed) (hxy : x ≠ y)
    (hfx : ∀ i, fn i ≠ x) (hfy : ∀ i, fn i ≠ y) :
    ArithmeticNamedProofConnectives.system A ⊢
      (NamedFiniteSyntax.Formula.all x (ArithmeticNamedOpenTranslation.formula seed ![x] fn φ)) 🡘
      (.all y (ArithmeticNamedOpenTranslation.formula seed ![y] fn φ)) :=
  body_alpha A φ seed x y fn hx hy hxy hfx hfy
example (A : SyntacticPredicates.Carrier) {n : ℕ} (x : Fin n)
    (φ : Semiformula ℒₒᵣ (Fin n) 0) (seed : ℕ) (hn : n ≤ seed) :
    ArithmeticNamedProofConnectives.system A ⊢
      (NamedFiniteSyntax.Formula.all x.val
        (ArithmeticNamedOpenTranslation.formula (seed+1) ![] Fin.val φ)) 🡘
      (.all seed (ArithmeticNamedOpenTranslation.formula (seed+1) ![seed] Fin.val
        (bindName x ▹ φ))) := closed_name_alpha A x φ seed hn
end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
