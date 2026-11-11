/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofConnectives


/-! # Statement checks in `V46ArithmeticNamedProofConnectivesChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofConnectivesChecks
open NamedArithmeticSignature ArithmeticNamedOpenTranslation ArithmeticNamedProofConnectives
local instance namedProofConnectivesChecksDecidableEq : DecidableEq NamedArithmeticSignature.Formula :=
  Classical.decEq _

example (Γ : SyntacticPredicates.Carrier) {ξ : Type} {n : ℕ}
    (φ : Semiformula ℒₒᵣ ξ n) (seed : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ) :
    system Γ ⊢ formula seed bn fn (∼φ) 🡘 (.neg (formula seed bn fn φ)) :=
  nnf_neg Γ φ seed bn fn

example (Γ : SyntacticPredicates.Carrier) {ξ : Type} {n : ℕ}
    (φ : Semiformula ℒₒᵣ ξ n) (low high : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ)
    (hb : ∀ i, bn i < low) (hf : ∀ i, fn i < low) (hle : low ≤ high) :
    system Γ ⊢ formula low bn fn φ 🡘 formula high bn fn φ :=
  seed_mono Γ φ low high bn fn hb hf hle

example (Γ : SyntacticPredicates.Carrier) (φ : Semiproposition ℒₒᵣ 1)
    (seed : ℕ) (fn : ℕ → ℕ) (δ : NamedArithmeticSignature.Formula)
    (hδ : seed ∉ δ.freeVariables)
    (h : SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ
      (.imp δ (formula (seed+1) ![] (freeCons seed fn) (Rewriting.free φ)))) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ
      (.imp δ (formula seed ![] fn (∀¹ φ))) :=
  lk_all_under Γ φ seed fn δ hδ h

example (Γ : SyntacticPredicates.Carrier) (φ : Semiproposition ℒₒᵣ 1)
    (t : SyntacticTerm ℒₒᵣ) (seed : ℕ) (fn : ℕ → ℕ) (hf : ∀ i, fn i < seed) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ
      (.imp (formula seed ![] fn (φ/[t])) (formula seed ![] fn (∃¹ φ))) :=
  lk_exs_instance Γ φ t seed fn hf


example (Γ : SyntacticPredicates.Carrier) (x : ℕ)
    (φ δ : NamedArithmeticSignature.Formula) (hx : x ∉ δ.freeVariables) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ
      (.imp (.all x (ArithmeticNamedTranslation.disjunction φ δ))
        (ArithmeticNamedTranslation.disjunction (.all x φ) δ)) :=
  all_disjunction_right Γ x φ δ hx

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofConnectivesChecks
