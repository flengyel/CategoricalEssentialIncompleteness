/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedNumericalSemantics


/-! # Statement checks in `V46NamedNumericalSemanticsChecks` -/

@[expose] public section
universe w
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedNumericalSemanticsChecks
open SyntacticSyntax NamedPostfixEncoding ConcreteNamedSubstitution NamedPlainSemantics
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
example (x : ℕ) (t : Obj 𝗣𝗔 ℕ X) (φ ψ : Obj 𝗣𝗔 ℕ Y) :
    substitutionResult variableCarrier σ π d x t.val φ.val = ok ψ.val ↔
      (decodeFormula σ π d φ).substitute x (decodeTerm σ π d t) =
        some (decodeFormula σ π d ψ) :=
  numerical_substitution_some_iff σ π d x t φ ψ
example (x : ℕ) (t : Obj 𝗣𝗔 ℕ X) (φ : Obj 𝗣𝗔 ℕ Y) :
    substitutionFreeFor variableCarrier σ π d x t.val φ.val = 1 ↔
      (decodeFormula σ π d φ).FreeFor x (decodeTerm σ π d t) :=
  numerical_freeFor_iff σ π d x t φ
example {K : Type w}
    (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
    (x : ℕ) (t r out : Obj 𝗣𝗔 ℕ X) (ρ : ℕ → K)
    (h : substitutionResult variableCarrier σ π d x t.val r.val = out.val) :
    evaluate σ π d functions out ρ = evaluate σ π d functions r
      (Function.update ρ x (evaluate σ π d functions t ρ)) :=
  numerical_evaluate_substitute σ π d functions x t r out ρ h
example {K : Type w}
    (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
    (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
    (x : ℕ) (t : Obj 𝗣𝗔 ℕ X) (φ ψ : Obj 𝗣𝗔 ℕ Y) (ρ : ℕ → K)
    (h : substitutionResult variableCarrier σ π d x t.val φ.val = ok ψ.val) :
    Holds σ π d functions relations ψ ρ ↔
      Holds σ π d functions relations φ
        (Function.update ρ x (evaluate σ π d functions t ρ)) :=
  numerical_holds_substitute σ π d functions relations x t φ ψ ρ h
end CategoricalEssentialIncompleteness.V46.NamedNumericalSemanticsChecks
