import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedSubstitution
import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution

/-! Standard output comparison for a generic finite named formula. The
numerals are exactly the checked zero/add-one constructor chain, and no
old canonical-numeral syntax identity is used. -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticFixedSubstitution
open NamedArithmeticSignature NamedArithmeticNumerals NamedPostfixEncoding
open ConcreteNamedSubstitution SyntacticSyntax

 theorem standard_literal_result (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      value φ n = NamedArithmeticSignature.formulaCode out ∧ out.freeVariables = [] := by
  have hff := value_admissible (M := ℕ) φ n
  rw [numeralCode_standard,natCast_nat] at hff
  have hFreeFor : φ.FreeFor 0 (numeral n) :=
    (substitutionFreeFor_formulaCode (σ := functionSymbols) (π := relationSymbols) (d := bound) φ (numeral n) 0).mp hff
  have hs := (NamedFiniteSyntax.Formula.substitute_isSome_iff φ 0 (numeral n)).mpr hFreeFor
  cases hsub : φ.substitute 0 (numeral n) with
  | none => simp [hsub] at hs
  | some out =>
    have hcode : value φ n = NamedArithmeticSignature.formulaCode out := by
      unfold value
      rw [numeralCode_standard,natCast_nat]
      change π₁ (substitutionResult variableSymbols functionSymbols relationSymbols bound
        0 (NamedArithmeticSignature.termCode (numeral n)) (NamedArithmeticSignature.formulaCode φ)) = NamedArithmeticSignature.formulaCode out
      rw [substitutionResult_formulaCode (σ := functionSymbols) (π := relationSymbols) (d := bound),hsub,optionCode,pi₁_pair]
    have hvars : freeVariables variableSymbols functionSymbols relationSymbols bound (NamedArithmeticSignature.formulaCode out) =
        NatVectors.pack out.freeVariables :=
      NamedPostfixEncoding.freeVariables_formulaCode (σ := functionSymbols) (π := relationSymbols) (d := bound) out
    have hp : NatVectors.pack out.freeVariables = 0 :=
      hvars.symm.trans ((congrArg (freeVariables variableSymbols functionSymbols relationSymbols bound) hcode).symm.trans
        (value_closed (M := ℕ) φ hφ n))
    exact ⟨out,rfl,hcode,(pack_eq_zero out.freeVariables).mp hp⟩

end CategoricalEssentialIncompleteness.V46.NamedArithmeticFixedSubstitution
