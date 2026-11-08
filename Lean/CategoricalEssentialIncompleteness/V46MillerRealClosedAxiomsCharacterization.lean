import CategoricalEssentialIncompleteness.V46MillerRealClosedAxiomsSemantics
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.Ring

/-! # The chosen recursive RCF axioms characterize real closure

For an arbitrary supplied ordered field, validity of the literal positive
square-root sentence and all literal odd Horner-root sentences supplies
the two criteria in the existing IsRealClosed.of_linearOrderedField theorem.
The converse uses the already constructed semantics of the same words.
This is a model characterization of the actual axiom set, not a truth
assumption for an arbitrary consistent extension.
-/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Polynomial
open scoped BigOperators
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Characterization
open OrderedFieldSyntax Semantics
universe u
variable {K : Type u} [Field K] [ord : LinearOrder K] [IsStrictOrderedRing K]
variable (constants : ℕ → K)

omit [IsStrictOrderedRing K] in
/-- Instantiate all the actual universal binders at the given assignment. -/
theorem close_elim (names : List ℕ) (φ : Formula) (ρ : ℕ → K)
    (h : Holds constants (close names φ) ρ) : Holds constants φ ρ := by
  induction names generalizing ρ with
  | nil => exact h
  | cons name names ih =>
      change ∀ x,Holds constants (close names φ) (Function.update ρ name x) at h
      simpa only [Function.update_eq_self] using ih _ (h (ρ name))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Coefficients are in ascending order, exactly as in the printed
Horner term. The final zero remains the original literal zero. -/
theorem horner_append_singleton (coefficients : List K) (a : K) :
    hornerPolynomial (coefficients++[a])=
      hornerPolynomial coefficients+C a*X^coefficients.length := by
  induction coefficients with
  | nil => simp [hornerPolynomial]
  | cons b coefficients ih =>
      change C b+X*hornerPolynomial (coefficients++[a])=
        (C b+X*hornerPolynomial coefficients)+C a*X^(coefficients.length+1)
      rw [ih,pow_succ]
      ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem horner_range_sum (coefficients : ℕ → K) (n : ℕ) :
    hornerPolynomial ((List.range n).map coefficients)=
      ∑ i∈Finset.range n,C (coefficients i)*X^i := by
  induction n with
  | zero => simp [hornerPolynomial]
  | succ n ih =>
      rw [List.range_succ,List.map_append,List.map_cons,List.map_nil,
        horner_append_singleton,List.length_map,List.length_range,ih,Finset.sum_range_succ]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Every polynomial, not only a supplied Horner presentation, is covered
by the literal scheme at its actual coefficient assignment. -/
theorem horner_coefficients (f : K[X]) :
    hornerPolynomial ((List.range (f.natDegree+1)).map f.coeff)=f := by
  rw [horner_range_sum]
  exact f.as_sum_range_C_mul_X_pow.symm

omit [IsStrictOrderedRing K] in
/-- Positive-square validity includes the missing zero case by its actual
zero witness, yielding precisely the nonnegative-square criterion. -/
theorem isSquare_of_nonneg_of_positiveSquare
    (h : ∀ ρ : ℕ → K,Holds constants positiveSquare ρ) {x : K} (hx : @LE.le K ord.toPartialOrder.toPreorder.toLE 0 x) : IsSquare x := by
  have hs : ∀ x : K,0<x → ∃ y : K,y*y=x := by
    simpa [positiveSquare] using h (fun _ => 0)
  rcases eq_or_lt_of_le hx with hx | hx
  · subst x
    exact ⟨0,by simp⟩
  · obtain ⟨y,hy⟩ := hs x hx
    exact ⟨y,hy.symm⟩

omit [IsStrictOrderedRing K] in
/-- Universal coefficient variables recover an arbitrary odd-degree
polynomial. The root variable is degree+1 and is distinct from every
coefficient variable; value_horner_update retains this distinction. -/
theorem odd_root_of_oddSentences
    (h : ∀ n : ℕ,∀ ρ : ℕ → K,Holds constants (oddSentence n) ρ)
    (f : K[X]) (hf : Odd f.natDegree) : ∃ x : K,f.IsRoot x := by
  obtain ⟨n,hn⟩ := hf
  have hd : f.natDegree=2*n+1 := by omega
  have hf0 : f≠0 := by
    intro he
    rw [he,natDegree_zero] at hd
    omega
  have hleading : f.coeff (2*n+1)≠0 := by
    rw [← hd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hf0
  have hb : Holds constants (oddBody (2*n+1)) f.coeff :=
    close_elim constants (List.range (2*n+2)) (oddBody (2*n+1)) f.coeff (h n f.coeff)
  simp only [oddBody,holds_imp,holds_negation,holds_equal,value_var,value_zero,
    holds_existential] at hb
  obtain ⟨x,hx⟩ := hb hleading
  rw [value_horner_update] at hx
  have hcoeff : hornerPolynomial ((List.range (2*n+1+1)).map f.coeff)=f := by
    rw [← hd]
    exact horner_coefficients f
  rw [hcoeff] at hx
  exact ⟨x,hx⟩

/-- No characterization or root-existence field is assumed: both criteria
are derived from the actual named sentences. -/
theorem isRealClosed_of_scheme_validity
    (hSquare : ∀ ρ : ℕ → K,Holds constants positiveSquare ρ)
    (hOdd : ∀ n : ℕ,∀ ρ : ℕ → K,Holds constants (oddSentence n) ρ) : IsRealClosed K :=
  IsRealClosed.of_linearOrderedField
    (fun hx => isSquare_of_nonneg_of_positiveSquare constants hSquare hx)
    (fun hf => odd_root_of_oddSentences constants hOdd _ hf)

/-- Satisfaction of the original word axiom set in the actual field
interpretation. The words and decoded named formulas are unchanged. -/
def ModelsWords (A : Set ℕ) : Prop := ∀ word∈A,
  ∃ φ : Formula,formulaCode φ=word ∧ ∀ ρ : ℕ → K,Holds constants φ ρ

omit [IsStrictOrderedRing K] in
theorem formula_valid_of_models {A : Set ℕ} (h : ModelsWords constants A)
    (φ : Formula) (hφ : formulaCode φ∈A) : ∀ ρ : ℕ → K,Holds constants φ ρ := by
  obtain ⟨ψ,hcode,hvalid⟩ := h (formulaCode φ) hφ
  have he : ψ=φ := NamedPostfixEncoding.formulaCode_injective hcode
  exact he ▸ hvalid

/-- This is the converse missing from the forward-validity module. -/
theorem isRealClosed_of_models (h : ModelsWords constants RCFAxiomWords) : IsRealClosed K :=
  isRealClosed_of_scheme_validity constants
    (formula_valid_of_models constants h positiveSquare positiveSquare_mem)
    (fun n => formula_valid_of_models constants h (oddSentence n) (oddSentence_mem n))

/-- Exact identification of the chosen recursive axiom set on every
supplied ordered field, with arbitrary interpretations of c_n. -/
theorem modelsRCF_iff_isRealClosed : ModelsWords constants RCFAxiomWords ↔ IsRealClosed K := by
  constructor
  · exact isRealClosed_of_models constants
  · intro h
    let : IsRealClosed K := h
    intro word hw
    exact Semantics.rcf_words_valid constants word hw

theorem formula_axioms_iff_isRealClosed :
    (∀ φ : Formula,formulaCode φ∈RCFAxiomWords → ∀ ρ : ℕ → K,Holds constants φ ρ) ↔ IsRealClosed K := by
  constructor
  · intro h
    exact isRealClosed_of_scheme_validity constants
      (h positiveSquare positiveSquare_mem) (fun n => h (oddSentence n) (oddSentence_mem n))
  · intro h φ hφ
    exact formula_valid_of_models constants ((modelsRCF_iff_isRealClosed constants).mpr h) φ hφ

/-- The actual T_a adds precisely its original strict cut sentences to
that real-closed-field axiom set. This concerns T_a, not arbitrary Γ. -/
theorem modelsTheory_iff (a : Point) : ModelsWords constants (theoryAxioms a) ↔
    IsRealClosed K ∧ ModelsWords constants (cutAxioms a) := by
  constructor
  · intro h
    exact ⟨(modelsRCF_iff_isRealClosed constants).mp (fun word hw => h word (Or.inl hw)),
      fun word hw => h word (Or.inr hw)⟩
  · rintro ⟨hrcf,hcut⟩ word (hword | hword)
    · exact ((modelsRCF_iff_isRealClosed constants).mpr hrcf) word hword
    · exact hcut word hword

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Characterization
