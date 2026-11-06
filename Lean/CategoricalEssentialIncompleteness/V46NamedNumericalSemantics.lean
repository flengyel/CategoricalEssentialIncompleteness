/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedPlainSemantics
import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution

/-! # Semantic substitution for the actual standard numerical algorithm -/

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding ConcreteNamedSubstitution
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)

theorem numerical_termSubstitution_result (x : ℕ) (t r : Obj 𝗣𝗔 ℕ X) :
    substitutionResult variableCarrier σ π d x t.val r.val =
      termCode ((decodeTerm σ π d r).substitute x (decodeTerm σ π d t)) := by
  have h := substitutionResult_termCode π (decodeTerm σ π d r) (decodeTerm σ π d t) x
  simpa only [decodeTerm_code] using h

/-- This is the actual numerical traversal at arbitrary standard
accepted inputs, rather than a new encoding of its claimed output. -/
theorem numerical_substitution_result (x : ℕ) (t : Obj 𝗣𝗔 ℕ X) (φ : Obj 𝗣𝗔 ℕ Y) :
    substitutionResult variableCarrier σ π d x t.val φ.val =
      optionCode ((decodeFormula σ π d φ).substitute x (decodeTerm σ π d t)) := by
  have h := substitutionResult_formulaCode (decodeFormula σ π d φ) (decodeTerm σ π d t) x
  simpa only [decodeFormula_code,decodeTerm_code] using h

/-- Successful numerical output identifies the literal named formula
substitution. Option-code injectivity preserves the failure branch. -/
theorem numerical_substitution_some_iff (x : ℕ) (t : Obj 𝗣𝗔 ℕ X)
    (φ ψ : Obj 𝗣𝗔 ℕ Y) :
    substitutionResult variableCarrier σ π d x t.val φ.val = ok ψ.val ↔
      (decodeFormula σ π d φ).substitute x (decodeTerm σ π d t) =
        some (decodeFormula σ π d ψ) := by
  rw [numerical_substitution_result]
  have he : ok ψ.val = optionCode (some (decodeFormula σ π d ψ)) := by
    simp only [ok,optionCode_some,decodeFormula_code]
  rw [he]
  exact optionCode_injective.eq_iff

theorem numerical_freeFor_iff (x : ℕ) (t : Obj 𝗣𝗔 ℕ X) (φ : Obj 𝗣𝗔 ℕ Y) :
    substitutionFreeFor variableCarrier σ π d x t.val φ.val = 1 ↔
      (decodeFormula σ π d φ).FreeFor x (decodeTerm σ π d t) := by
  have h := substitutionFreeFor_formulaCode (decodeFormula σ π d φ) (decodeTerm σ π d t) x
  simpa only [decodeFormula_code,decodeTerm_code] using h

variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

theorem numerical_evaluate_substitute (x : ℕ) (t r out : Obj 𝗣𝗔 ℕ X) (ρ : ℕ → K)
    (h : substitutionResult variableCarrier σ π d x t.val r.val = out.val) :
    evaluate σ π d functions out ρ = evaluate σ π d functions r
      (Function.update ρ x (evaluate σ π d functions t ρ)) := by
  have he : (decodeTerm σ π d r).substitute x (decodeTerm σ π d t) = decodeTerm σ π d out :=
    termCode_injective ((numerical_termSubstitution_result σ π d x t r).symm.trans
      (h.trans (decodeTerm_code σ π d out).symm))
  change (decodeTerm σ π d out).evaluate functions ρ = _
  rw [← he]
  exact NamedFiniteSyntax.Term.evaluate_substitute functions
    (decodeTerm σ π d r) (decodeTerm σ π d t) x ρ

/-- The semantic structure K is independent of the standard arithmetic
code model. The actual categorical admissibility comparison supplies
this numerical success equation in Lemma 6.5's application. -/
theorem numerical_holds_substitute (x : ℕ) (t : Obj 𝗣𝗔 ℕ X)
    (φ ψ : Obj 𝗣𝗔 ℕ Y) (ρ : ℕ → K)
    (h : substitutionResult variableCarrier σ π d x t.val φ.val = ok ψ.val) :
    Holds σ π d functions relations ψ ρ ↔
      Holds σ π d functions relations φ
        (Function.update ρ x (evaluate σ π d functions t ρ)) := by
  exact NamedFiniteSyntax.Formula.holds_substitute functions relations
    (decodeFormula σ π d φ) (decodeFormula σ π d ψ) (decodeTerm σ π d t) x ρ
    ((numerical_substitution_some_iff σ π d x t φ ψ).mp h)

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
