import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonBasic

/-! # Direct comparison of the arithmetic/order axiom matrices -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
open NamedArithmeticSignature ArithmeticNamedProofConnectives
local instance matrixComparisonDecidableEq : DecidableEq Fm := Classical.decEq _
variable (A : SyntacticPredicates.Carrier)
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
local notation "S" => ArithmeticNamedProofConnectives.system A

private theorem fromClosure (hΓ : ExtendsPA A) (names : List ℕ) (φ : Fm)
    (hφ : PASeed φ) (hc : (closure names φ).freeVariables = []) : D (closure names φ) :=
  hΓ _ ⟨hc,φ,hφ,closure_isUniversal names φ⟩

private theorem of_equivalence {φ ψ : Fm} (h : S ⊢ φ 🡘 ψ) (hp : D ψ) : D φ :=
  (NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
    (ArithmeticNamedProofConnectives.system A) φ).mp
      ((K_right h) ⨀ ((NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
        (ArithmeticNamedProofConnectives.system A) ψ).mpr hp))

theorem addZero_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addZero) := by
  exact fromClosure A hΓ [0] _ (PASeed.addZero 0) (by decide)

theorem addAssoc_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addAssoc) := by
  exact fromClosure A hΓ [0,1,2] _ (PASeed.addAssoc 0 1 2) (by decide)

theorem addComm_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addComm) := by
  exact fromClosure A hΓ [0,1] _ (PASeed.addComm 0 1) (by decide)

theorem addEqOfLt_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addEqOfLt) := by
  have hp := fromClosure A hΓ [0,1] _ (PASeed.addEqOfLt 0 1 2 (by decide) (by decide)) (by decide)
  have he := all_equivalence A 0 (all_equivalence A 1
    (implication A (“#1 < #0” : ArithmeticSemisentence 2)
      (“∃ z, #2 + z = #1” : ArithmeticSemisentence 2) 2 ![1,0] Empty.elim))
  exact of_equivalence A he hp

theorem zeroLe_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.zeroLe) := by
  exact fromClosure A hΓ [0] _ (PASeed.zeroLe 0) (by decide)

theorem zeroLtOne_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.zeroLtOne) := by
  exact fromClosure A hΓ [] _ PASeed.zeroLtOne (by decide)

theorem oneLeOfZeroLt_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.oneLeOfZeroLt) := by
  have hp := fromClosure A hΓ [0] _ (PASeed.oneLeOfZeroLt 0) (by decide)
  have he := all_equivalence A 0
    (implication A (“0 < #0” : ArithmeticSemisentence 1)
      (“1 ≤ #0” : ArithmeticSemisentence 1) 1 ![0] Empty.elim)
  exact of_equivalence A he hp

theorem addLtAdd_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addLtAdd) := by
  have hp := fromClosure A hΓ [0,1,2] _ (PASeed.addLtAdd 0 1 2) (by decide)
  have he := all_equivalence A 0 (all_equivalence A 1 (all_equivalence A 2
    (implication A (“#2 < #1” : ArithmeticSemisentence 3)
      (“#2 + #0 < #1 + #0” : ArithmeticSemisentence 3) 3 ![2,1,0] Empty.elim)))
  exact of_equivalence A he hp

theorem mulZero_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulZero) := by
  exact fromClosure A hΓ [0] _ (PASeed.mulZero 0) (by decide)

theorem mulOne_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulOne) := by
  exact fromClosure A hΓ [0] _ (PASeed.mulOne 0) (by decide)

theorem mulAssoc_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulAssoc) := by
  exact fromClosure A hΓ [0,1,2] _ (PASeed.mulAssoc 0 1 2) (by decide)

theorem mulComm_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulComm) := by
  exact fromClosure A hΓ [0,1] _ (PASeed.mulComm 0 1) (by decide)

theorem mulLtMul_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulLtMul) := by
  have hp := fromClosure A hΓ [0,1,2] _ (PASeed.mulLtMul 0 1 2) (by decide)
  have he := all_equivalence A 0 (all_equivalence A 1 (all_equivalence A 2
    (implication A (“#2 < #1 ∧ 0 < #0” : ArithmeticSemisentence 3)
      (“#2 * #0 < #1 * #0” : ArithmeticSemisentence 3) 3 ![2,1,0] Empty.elim)))
  exact of_equivalence A he hp

theorem distr_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.distr) := by
  exact fromClosure A hΓ [0,1,2] _ (PASeed.distr 0 1 2) (by decide)

theorem ltIrrefl_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.ltIrrefl) := by
  exact fromClosure A hΓ [0] _ (PASeed.ltIrrefl 0) (by decide)

theorem ltTrans_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.ltTrans) := by
  have hp := fromClosure A hΓ [0,1,2] _ (PASeed.ltTrans 0 1 2) (by decide)
  have he := all_equivalence A 0 (all_equivalence A 1 (all_equivalence A 2
    (implication A (“#2 < #1 ∧ #1 < #0” : ArithmeticSemisentence 3)
      (“#2 < #0” : ArithmeticSemisentence 3) 3 ![2,1,0] Empty.elim)))
  exact of_equivalence A he hp

theorem ltTri_admissible (hΓ : ExtendsPA A) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.ltTri) := by
  exact fromClosure A hΓ [0,1] _ (PASeed.ltTri 0 1) (by decide)

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
