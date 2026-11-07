import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationClosure

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.ClosureChecks
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

example (φ ψ : Formula) :
    closureRelation.val.Evalb ![formulaCode ψ,formulaCode φ] ↔ UniversalClosure φ ψ :=
  closureRelation_codes φ ψ

example (φ ψ : Formula) (names : ℕ)
    (h : (SyntacticDerivation.Records.run closureStep).val.Evalb
      ![names,formulaCode ψ,formulaCode φ]) : UniversalClosure φ ψ :=
  closure_run_codes φ ψ names h

example {φ ψ : Formula} (h : UniversalClosure φ ψ) :
    ∃ names : ℕ, (SyntacticDerivation.Records.run closureStep).val.Evalb
      ![names,formulaCode ψ,formulaCode φ] := closure_record h

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.ClosureChecks
