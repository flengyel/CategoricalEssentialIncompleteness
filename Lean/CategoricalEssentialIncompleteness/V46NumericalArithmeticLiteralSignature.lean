/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticSignatureRelabel
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralVariables
import CategoricalEssentialIncompleteness.V46NumericalArithmeticPA

/-! # The chosen arithmetic signature and its actual numerical code labels -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LiteralSignature
open NamedFiniteSyntax NamedPostfixEncoding

/-- The literal quasi-inverse uses the actual unary numerical object,
including its proved coefficient-code membership. -/
def coefficients (σ : ℕ → Carrier) (k : ℕ) : Carrier :=
  NumericalCoordinates.codedPredicate (NumericalCoordinates.predicateObject (σ k : PredicateCategory 𝗧𝗔))

theorem coefficient_membership (σ : ℕ → Carrier) (k n : ℕ) :
    (σ k).val.Evalb ![n] ↔ (coefficients σ k).val.Evalb ![n] :=
  (NumericalNamed.codedPredicate_predicateObject_eval (σ k : PredicateCategory 𝗧𝗔) n).symm

variable {σ π : ℕ → Carrier} {d : ℕ}

def termEquiv : Term (Symbols σ) d ≃ Term (Symbols (coefficients σ)) d :=
  SignatureRelabel.termEquiv (coefficient_membership σ)

def formulaEquiv : Formula (Symbols σ) (Symbols π) d ≃
    Formula (Symbols (coefficients σ)) (Symbols (coefficients π)) d :=
  SignatureRelabel.formulaEquiv (coefficient_membership σ) (coefficient_membership π)

@[simp] theorem term_code (t : Term (Symbols σ) d) :
    termCode (termEquiv t) = termCode t := SignatureRelabel.term_code (coefficient_membership σ) t

@[simp] theorem formula_code (φ : Formula (Symbols σ) (Symbols π) d) :
    formulaCode (formulaEquiv φ) = formulaCode φ :=
  SignatureRelabel.formula_code (coefficient_membership σ) (coefficient_membership π) φ

@[simp] theorem freeVariables (φ : Formula (Symbols σ) (Symbols π) d) :
    (formulaEquiv φ).freeVariables = φ.freeVariables :=
  SignatureRelabel.formula_freeVariables (coefficient_membership σ) (coefficient_membership π) φ

theorem substitute (φ : Formula (Symbols σ) (Symbols π) d) (x : ℕ) (t : Term (Symbols σ) d) :
    Option.map formulaEquiv (φ.substitute x t) = (formulaEquiv φ).substitute x (termEquiv t) :=
  SignatureRelabel.formula_substitute (coefficient_membership σ) (coefficient_membership π) φ x t

theorem freeFor (φ : Formula (Symbols σ) (Symbols π) d) (x : ℕ) (t : Term (Symbols σ) d) :
    (formulaEquiv φ).FreeFor x (termEquiv t) ↔ φ.FreeFor x t :=
  SignatureRelabel.formula_freeFor (coefficient_membership σ) (coefficient_membership π) φ x t

/-- The literal Gamma axiom predicate is unchanged because formula codes,
binder names, and all ordered children are unchanged. -/
theorem derives_iff (Γ : Carrier) (φ : Formula (Symbols σ) (Symbols π) d) :
    SyntacticNamedHilbert.Derives (coefficients σ) (coefficients π) d Γ (formulaEquiv φ) ↔
      SyntacticNamedHilbert.Derives σ π d Γ φ :=
  SignatureRelabel.derives_iff (coefficient_membership σ) (coefficient_membership π) Γ φ

/-- The arithmetic instance uses the already chosen PA sentence axioms;
there is no residual admissibility premise. -/
theorem arithmetic_PA (Γ : Carrier) (hΓ : NumericalArithmetic.ContainsPA Γ)
    (φ : NamedArithmeticSignature.Formula) (hφ : ArithmeticNamedAxiomComparison.PAAxiom φ) :
    SyntacticNamedHilbert.Derives (coefficients NamedArithmeticSignature.functionSymbols)
      (coefficients NamedArithmeticSignature.relationSymbols) NamedArithmeticSignature.bound Γ
      (formulaEquiv φ) :=
  (derives_iff Γ φ).mpr (NumericalArithmetic.extendsPA Γ hΓ φ hφ)

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LiteralSignature
