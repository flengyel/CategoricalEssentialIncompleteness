import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedStandard
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open NamedArithmeticSignature NamedArithmeticFixedSubstitution
example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      value φ n = NamedArithmeticSignature.formulaCode out ∧ out.freeVariables = [] :=
  standard_literal_result φ hφ n
