/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixFreeVariables
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAlgorithmTyped

/-! # The numerical substitution traversal on standard named syntax -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
open ConcreteNamedSubstitution
variable {σ π : ℕ → Carrier} {d : ℕ}

local instance namedPostfixSubstitutionPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem adjoin_zero_numeric (x : ℕ) : adjoin x (0 : ℕ) = Nat.pair x 0 + 1 := by
  rw [FiniteSigmaOne.canonical_adjoin,nat_pair_eq]

private theorem allChildren_termPower (g : ℕ → ℕ) (n : ℕ) (u : ℕ) :
    allChildren (fun _ => 1) g (SyntaxPolynomial.power .term n) u = 1 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n => simp [SyntaxPolynomial.power,allChildren,ih]

private theorem allChildren_constructors (π : ℕ → Carrier) (g : ℕ → ℕ) (n : ℕ) (u : ℕ) :
    allChildren (fun _ => 1) g (SyntaxPolynomial.constructors π n) u = 1 := by
  induction n generalizing u with
  | zero => simp [SyntaxPolynomial.constructors,allChildren,allChildren_termPower]
  | succ n ih => simp [SyntaxPolynomial.constructors,allChildren,allChildren_termPower,ih]

theorem substitutionPayload_termCode (π : ℕ → Carrier)
    (r t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionPayload variableCarrier σ π d x (termCode t) (termCode r) =
      payload (termCode r) (pack r.freeVariables) (termCode (r.substitute x t)) 1 := by
  induction r with
  | var y =>
      rw [termCode_root (.var y)]
      erw [substitutionPayload_term_constructor variableCarrier σ π d _ _ _
        (termInput_member π (.var y))]
      by_cases he : y = x <;>
        simp [termInput,termRoot,termPolynomial,SyntaxPolynomial.termExpression,mapChildren,
          NamedFiniteSyntax.Term.substitute,NamedFiniteSyntax.Term.freeVariables,
          freeVarsTermRoot,termCode,he,adjoin_zero_numeric]
  | app k s children ih =>
      rw [termCode_root (.app k s children)]
      erw [substitutionPayload_term_constructor variableCarrier σ π d _ _ _
        (termInput_member π (.app k s children))]
      simp [termInput,termRoot,termPolynomial,SyntaxPolynomial.termExpression,mapChildren,
        NamedFiniteSyntax.Term.substitute,NamedFiniteSyntax.Term.freeVariables,
        freeVarsTermRoot,termCode,ih]

theorem substitutionPayload_formulaCode
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionPayload variableCarrier σ π d x (termCode t) (formulaCode φ) =
      payload (formulaCode φ) (pack φ.freeVariables) (optionCode (φ.substitute x t))
        (if φ.FreeFor x t then 1 else 0) := by
  classical
  induction φ with
  | equal r s =>
      rw [formulaCode_root]
      erw [substitutionPayload_formula_constructor variableCarrier σ π d _ _ _
        (formulaInput_member (.equal r s))]
      simp [formulaInput,equalInput,formulaRoot,formulaPolynomial,SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.power,mapChildren,allChildren,formulaLeft,freeVarsFormulaRoot,gather,
        substitutionPayload_termCode,ok,
        NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Formula.FreeFor,
        NamedFiniteSyntax.Formula.freeVariables,formulaCode]
  | relation k p children =>
      rw [formulaCode_root]
      erw [substitutionPayload_formula_constructor variableCarrier σ π d _ _ _
        (formulaInput_member (.relation k p children))]
      simp [formulaInput,relationInput,formulaRoot,formulaPolynomial,SyntaxPolynomial.formulaExpression,
        mapChildren,allChildren,allChildren_constructors,formulaLeft,freeVarsFormulaRoot,gather,
        substitutionPayload_termCode,ok,
        NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Formula.FreeFor,
        NamedFiniteSyntax.Formula.freeVariables,formulaCode]
  | neg body ih =>
      rw [formulaCode_root]
      erw [substitutionPayload_formula_constructor variableCarrier σ π d _ _ _
        (formulaInput_member (.neg body))]
      cases hs : body.substitute x t <;>
        simp [formulaInput,negInput,formulaRoot,formulaPolynomial,SyntaxPolynomial.formulaExpression,
          mapChildren,allChildren,formulaLeft,freeVarsFormulaRoot,gather,ih,
          successfulValue,success,ok,optionCode,pi₂_zero,hs,
          ← NamedFiniteSyntax.Formula.substitute_isSome_iff body x t,
          NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Formula.FreeFor,
          NamedFiniteSyntax.Formula.freeVariables,formulaCode]
  | imp left right il ir =>
      rw [formulaCode_root]
      erw [substitutionPayload_formula_constructor variableCarrier σ π d _ _ _
        (formulaInput_member (.imp left right))]
      cases hl : left.substitute x t <;> cases hr : right.substitute x t <;>
        simp [formulaInput,impInput,formulaRoot,formulaPolynomial,SyntaxPolynomial.formulaExpression,
          SyntaxPolynomial.power,mapChildren,allChildren,formulaLeft,freeVarsFormulaRoot,gather,il,ir,
          successfulValue,success,ok,optionCode,pi₂_zero,hl,hr,
          ← NamedFiniteSyntax.Formula.substitute_isSome_iff left x t,
          ← NamedFiniteSyntax.Formula.substitute_isSome_iff right x t,
          NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Formula.FreeFor,
          NamedFiniteSyntax.Formula.freeVariables,formulaCode]
  | all y body ih =>
      rw [formulaCode_root]
      erw [substitutionPayload_formula_constructor variableCarrier σ π d _ _ _
        (formulaInput_member (.all y body))]
      by_cases he : y = x <;>
      by_cases hc : x ∉ body.freeVariables ∨ y ∉ t.freeVariables <;>
      cases hs : body.substitute x t <;>
        simp [formulaInput,allInput,formulaRoot,formulaPolynomial,SyntaxPolynomial.formulaExpression,
          mapChildren,freeVarsFormulaRoot,ih,capture,freeVariables_termCode,
          successfulValue,success,ok,optionCode,pi₂_zero,he,hc,hs,
          ← NamedFiniteSyntax.Formula.substitute_isSome_iff body x t,
          NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Formula.FreeFor,
          NamedFiniteSyntax.Formula.freeVariables,formulaCode,bne,Bool.beq_eq_decide_eq]

@[simp] theorem substitutionResult_termCode (π : ℕ → Carrier)
    (r t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionResult variableCarrier σ π d x (termCode t) (termCode r) =
      termCode (r.substitute x t) := by
  simp only [substitutionResult,substitutionPayload_termCode,result_payload]

@[simp] theorem substitutionResult_formulaCode
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionResult variableCarrier σ π d x (termCode t) (formulaCode φ) =
      optionCode (φ.substitute x t) := by
  simp only [substitutionResult,substitutionPayload_formulaCode,result_payload]

theorem substitutionFreeFor_formulaCode
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionFreeFor variableCarrier σ π d x (termCode t) (formulaCode φ) = 1 ↔
      φ.FreeFor x t := by
  simp only [substitutionFreeFor,substitutionPayload_formulaCode,freeFor_payload]
  split_ifs <;> simp_all

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
