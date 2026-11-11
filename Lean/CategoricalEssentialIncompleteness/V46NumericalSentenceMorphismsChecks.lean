/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalSentenceMorphisms


/-! # Statement checks in `V46NumericalSentenceMorphismsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
open NamedArithmeticSignature NumericalSentenceMorphisms

example : omega.dimension = 1 := rfl
example : omega.support = Set.univ := rfl
example : omega ⟶ sentence := theta
  (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
  (NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val)

example (s : NumericalTuples.Point sentence) :
    (negation.toFun s).val = NamedArithmeticProofSearch.negationWord ℕ s.val := negation_value s

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      ((theta φ hφ).toFun (omegaPoint n)).val = formulaCode out ∧ out.freeVariables = [] :=
  standard_literal_result φ hφ n
