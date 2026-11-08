import CategoricalEssentialIncompleteness.V46MillerRealClosedAxiomsCharacterization

open Polynomial
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Characterization
open OrderedFieldSyntax Semantics
universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example (f : K[X]) :
    hornerPolynomial ((List.range (f.natDegree+1)).map f.coeff)=f := horner_coefficients f

example (constants : ℕ → K)
    (hSquare : ∀ ρ : ℕ → K,Holds constants positiveSquare ρ)
    (hOdd : ∀ n : ℕ,∀ ρ : ℕ → K,Holds constants (oddSentence n) ρ) : IsRealClosed K :=
  isRealClosed_of_scheme_validity constants hSquare hOdd

example (constants : ℕ → K) :
    (∀ word∈RCFAxiomWords,∃ φ : Formula,formulaCode φ=word ∧
      ∀ ρ : ℕ → K,φ.Holds (functions constants) (relations (K := K)) ρ) ↔ IsRealClosed K :=
  modelsRCF_iff_isRealClosed constants

example (constants : ℕ → K) :
    (∀ φ : Formula,formulaCode φ∈RCFAxiomWords →
      ∀ ρ : ℕ → K,φ.Holds (functions constants) (relations (K := K)) ρ) ↔ IsRealClosed K :=
  formula_axioms_iff_isRealClosed constants

example (constants : ℕ → K) (a : Point) :
    (∀ word∈RCFAxiomWords∪cutAxioms a,∃ φ : Formula,formulaCode φ=word ∧
      ∀ ρ : ℕ → K,φ.Holds (functions constants) (relations (K := K)) ρ) ↔
    IsRealClosed K ∧ (∀ word∈cutAxioms a,∃ φ : Formula,formulaCode φ=word ∧
      ∀ ρ : ℕ → K,φ.Holds (functions constants) (relations (K := K)) ρ) :=
  modelsTheory_iff constants a

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Characterization
