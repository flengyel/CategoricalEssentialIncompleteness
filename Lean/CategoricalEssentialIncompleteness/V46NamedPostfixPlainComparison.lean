/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixSemantics
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Standard named trees in the actual plain categorical syntax

The comparison uses the proved constructor-preserving plain-parser
isomorphism. Its action fixes the literal numerical word.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixPlainComparison
open NamedPostfixEncoding NamedPostfixSemantics SyntacticSyntax

/-- The actual interpreted comparison arrow keeps the same word in
any model of T, not merely at closed standard inputs. -/
theorem plainCarrierIso_value (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (sort : Bool) (a b : RawPolynomial) (word : Obj T M (Postfix.carrier sort a b)) :
    ((F T M).map (Postfix.plainCarrierIso T sort a b).hom word).val = word.val := by
  let out := (F T M).map (Postfix.plainCarrierIso T sort a b).hom word
  have hg := (PredicateInterpretation.map_class_eq_iff T M
    (Postfix.toPlainMorphism T sort a b) word out).mp rfl
  exact ((GraphMorphism.identityGraph_eval _ _ _).mp hg).2

def plainTermModelEquiv (σ π : ℕ → Carrier) (d : ℕ) :
    NamedFiniteSyntax.Term (Symbols σ) d ≃
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj
        (plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d).algebra.a.1 :=
  (termModelEquiv σ π d).trans
    (((PredicateInterpretation.functor 𝗣𝗔 ℕ).mapIso
      (Postfix.plainCarrierIso 𝗣𝗔 false (termPolynomial σ d) (formulaPolynomial π d))).toEquiv)

def plainFormulaModelEquiv (σ π : ℕ → Carrier) (d : ℕ) :
    NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d ≃
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj
        (plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d).algebra.a.2 :=
  (formulaModelEquiv σ π d).trans
    (((PredicateInterpretation.functor 𝗣𝗔 ℕ).mapIso
      (Postfix.plainCarrierIso 𝗣𝗔 true (termPolynomial σ d) (formulaPolynomial π d))).toEquiv)

@[simp] theorem plainTermModelEquiv_val {σ π : ℕ → Carrier} {d : ℕ}
    (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    (plainTermModelEquiv σ π d r).val = termCode r := by
  exact plainCarrierIso_value 𝗣𝗔 ℕ false (termPolynomial σ d) (formulaPolynomial π d)
    (termModelEquiv σ π d r)

@[simp] theorem plainFormulaModelEquiv_val {σ π : ℕ → Carrier} {d : ℕ}
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (plainFormulaModelEquiv σ π d φ).val = formulaCode φ := by
  exact plainCarrierIso_value 𝗣𝗔 ℕ true (termPolynomial σ d) (formulaPolynomial π d)
    (formulaModelEquiv σ π d φ)

end CategoricalEssentialIncompleteness.V46.NamedPostfixPlainComparison
