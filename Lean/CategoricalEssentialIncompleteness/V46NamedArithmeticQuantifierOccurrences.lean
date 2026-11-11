/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticModelOccurrences

/-! The actual quantified-constructor occurrence equation on arbitrary
internal child words. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticQuantifierOccurrences
open ConcreteNamedSubstitution NamedPostfixEncoding NamedArithmeticModelCoding
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "Tm" => Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)
local notation "Fm" => Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)
local notation "FV" => ConcreteNamedSubstitution.freeVariables variableCarrier σ π d

theorem quantifierInput_member (name body : M)
    (hn : variableCarrier.val.Evalb ![name]) (hb : (Fm).val.Evalb ![body]) :
    (rawCarrier Tm Fm (formulaPolynomial π d)).val.Evalb
      ![NamedArithmeticModelCoding.allInput name body] := by
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inr
  refine ⟨_, rfl, ?_⟩
  exact (rawCarrier_product_eval Tm Fm _ _ _).mpr ⟨name,body,rfl,hn,hb⟩

theorem quantifier_occurrences (name body : M)
    (hn : variableCarrier.val.Evalb ![name]) (hb : (Fm).val.Evalb ![body]) :
    FV (constructor true (formulaPolynomial π d) (NamedArithmeticModelCoding.allInput name body)) =
      delete name (FV body) := by
  erw [freeVariables_formula_constructor variableCarrier σ π d _
    (quantifierInput_member σ π d name body hn hb)]
  simp [NamedArithmeticModelCoding.allInput,SyntaxPolynomial.formulaExpression,
    mapChildren,freeVarsFormulaRoot]

end CategoricalEssentialIncompleteness.V46.NamedArithmeticQuantifierOccurrences
