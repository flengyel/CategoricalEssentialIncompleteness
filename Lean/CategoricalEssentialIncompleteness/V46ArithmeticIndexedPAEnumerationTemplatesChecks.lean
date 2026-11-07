import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationTemplates

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.TemplatesChecks
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

example (environment : ℕ) (term : TermSchema) :
    Words.value term.expression environment = termCode (term.instantiate environment) :=
  TermSchema.expression_code environment term

example (environment : ℕ) (formula : FormulaSchema) :
    Words.value formula.expression environment = formulaCode (formula.instantiate environment) :=
  FormulaSchema.expression_code environment formula

example (k : Fin 17) (environment : ℕ)
    (h : k.val = 3 →
      Words.value (.slot 2) environment ≠ Words.value (.slot 0) environment ∧
      Words.value (.slot 2) environment ≠ Words.value (.slot 1) environment) :
    PASeed ((simpleTemplate k).instantiate environment) := simpleTemplate_seed k environment h

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.TemplatesChecks
