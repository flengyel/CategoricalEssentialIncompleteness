/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedPostfixOperations
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariables

/-! # The actual standard occurrence algorithm computes named free variables -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
open ConcreteNamedSubstitution
variable {σ π : ℕ → Carrier} {d : ℕ}

@[simp] theorem freeVariables_termCode (π : ℕ → Carrier)
    (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (termCode r) =
      pack r.freeVariables := by
  induction r with
  | var x =>
      change ConcreteNamedSubstitution.freeVariables variableCarrier σ π d
        (constructor false (termPolynomial σ d) (Arithmetic.pair x 0)) = pack [x]
      rw [pack_adjoin, pack_nil]
      exact freeVariables_variable variableCarrier σ π d x (by simp [variableCarrier])
  | app k s children ih =>
      rw [termCode_root]
      erw [freeVariables_term_constructor variableCarrier σ π d _
        (termInput_member π (.app k s children))]
      simp [termInput, SyntaxPolynomial.termExpression,
        mapChildren, freeVarsTermRoot, ih, NamedFiniteSyntax.Term.freeVariables]

@[simp] theorem freeVariables_formulaCode
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (formulaCode φ) =
      pack φ.freeVariables := by
  induction φ with
  | equal r t =>
      rw [formulaCode_root]
      erw [freeVariables_formula_constructor variableCarrier σ π d _
        (formulaInput_member (.equal r t))]
      simp [formulaInput, equalInput, SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.power, mapChildren, freeVarsFormulaRoot, formulaLeft, gather,
        NamedFiniteSyntax.Formula.freeVariables]
  | relation k p children =>
      rw [formulaCode_root]
      erw [freeVariables_formula_constructor variableCarrier σ π d _
        (formulaInput_member (.relation k p children))]
      simp [formulaInput, relationInput, SyntaxPolynomial.formulaExpression,
        mapChildren, freeVarsFormulaRoot, formulaLeft, gather,
        NamedFiniteSyntax.Formula.freeVariables]
  | neg body ih =>
      rw [formulaCode_root]
      erw [freeVariables_formula_constructor variableCarrier σ π d _
        (formulaInput_member (.neg body))]
      simp [formulaInput, negInput, SyntaxPolynomial.formulaExpression,
        mapChildren, freeVarsFormulaRoot, formulaLeft, gather, ih,
        NamedFiniteSyntax.Formula.freeVariables]
  | imp left right il ir =>
      rw [formulaCode_root]
      erw [freeVariables_formula_constructor variableCarrier σ π d _
        (formulaInput_member (.imp left right))]
      simp [formulaInput, impInput, SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.power, mapChildren, freeVarsFormulaRoot, formulaLeft, gather, il, ir,
        NamedFiniteSyntax.Formula.freeVariables]
  | all name body ih =>
      change ConcreteNamedSubstitution.freeVariables variableCarrier σ π d
        (constructor true (formulaPolynomial π d) (allInput name (formulaCode body))) = _
      erw [freeVariables_quantifier variableCarrier σ π d name (formulaCode body)
        (by simp [variableCarrier]) (formulaCode_member body)]
      simp [ih, NamedFiniteSyntax.Formula.freeVariables, bne, Bool.beq_eq_decide_eq]

/-- Empty numerical occurrence list is precisely the named sentence
condition on the corresponding standard word. -/
theorem sentence_formulaCode_iff
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (formulaCode φ) = 0 ↔
      φ.freeVariables = [] := by
  rw [freeVariables_formulaCode, pack_eq_zero]

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
