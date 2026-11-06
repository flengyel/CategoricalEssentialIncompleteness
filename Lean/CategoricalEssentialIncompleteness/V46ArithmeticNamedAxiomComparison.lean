import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonMatrices
import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonEquality
import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonInduction

/-! # Concrete source PA admissibility for the literal named enumeration -/
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
open NamedArithmeticSignature
variable (A : SyntacticPredicates.Carrier)
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A

theorem equality_admissible {φ : ArithmeticSentence} (h : φ ∈ Theory.eqAxiom ℒₒᵣ) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] φ) := by
  cases h with
  | refl => exact eqRefl_admissible A
  | symm => exact eqSymm_admissible A
  | trans => exact eqTrans_admissible A
  | funcExt f =>
      cases f with
      | zero => exact eqZeroExt_admissible A
      | one => exact eqOneExt_admissible A
      | add => exact eqAddExt_admissible A
      | mul => exact eqMulExt_admissible A
  | relExt r =>
      cases r with
      | eq => exact eqEqRelExt_admissible A
      | lt => exact eqLtRelExt_admissible A

theorem peanoMinus_admissible (hΓ : ExtendsPA A) {φ : ArithmeticSentence}
    (h : φ ∈ 𝗣𝗔⁻) : D (ArithmeticNamedTranslation.translateFormula 0 ![] φ) := by
  cases h with
  | equal φ hφ => exact equality_admissible A hφ
  | addZero => exact addZero_admissible A hΓ
  | addAssoc => exact addAssoc_admissible A hΓ
  | addComm => exact addComm_admissible A hΓ
  | addEqOfLt => exact addEqOfLt_admissible A hΓ
  | zeroLe => exact zeroLe_admissible A hΓ
  | zeroLtOne => exact zeroLtOne_admissible A hΓ
  | oneLeOfZeroLt => exact oneLeOfZeroLt_admissible A hΓ
  | addLtAdd => exact addLtAdd_admissible A hΓ
  | mulZero => exact mulZero_admissible A hΓ
  | mulOne => exact mulOne_admissible A hΓ
  | mulAssoc => exact mulAssoc_admissible A hΓ
  | mulComm => exact mulComm_admissible A hΓ
  | mulLtMul => exact mulLtMul_admissible A hΓ
  | distr => exact distr_admissible A hΓ
  | ltIrrefl => exact ltIrrefl_admissible A hΓ
  | ltTrans => exact ltTrans_admissible A hΓ
  | ltTri => exact ltTri_admissible A hΓ

/-- The printed native Γ≥PA condition supplies the actual source PA
axioms needed by the previously proved finite-proof translation. -/
theorem axiomsAdmissible_PA (hΓ : ExtendsPA A) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔 := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact peanoMinus_admissible A hΓ hφ
  · obtain ⟨ψ,_,rfl⟩ := hφ
    exact induction_admissible A hΓ ψ

theorem axiomsAdmissible_of_extendsPA (hΓ : ExtendsPA A) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔 :=
  axiomsAdmissible_PA A hΓ

/-- An individual finite source PA proof is translated into an actual
literal named Γ proof under the printed native PA extension condition. -/
theorem sentence_PA_of_extendsPA (hΓ : ExtendsPA A) (φ : ArithmeticSentence)
    (hφ : 𝗣𝗔 ⊢ φ) : D (ArithmeticNamedTranslation.translateFormula 0 ![] φ) :=
  ArithmeticNamedProofTranslation.sentence A 𝗣𝗔 (axiomsAdmissible_PA A hΓ) φ hφ

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
