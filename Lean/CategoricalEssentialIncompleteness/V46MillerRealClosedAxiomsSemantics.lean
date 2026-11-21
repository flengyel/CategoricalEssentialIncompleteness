/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedAxioms
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.Real.Sqrt

/-! # Literal field-axiom semantics and the real model of T_a

The polynomial-root premise in the generic theorem is the standard
IsRealClosed class. Its real-number instance is constructed below from
the proved real polynomial sign theorems and square roots. No truth
assumption is made for a consistent extension of the word axiom set.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Semantics
open OrderedFieldSyntax
open Polynomial
universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def functions (constants : ℕ → K) : (n : Fin (bound+1)) →
    FunctionSymbols n.val → (Fin n.val → K) → K
  | ⟨0,_⟩,symbol,_ => if symbol.val=0 then 0 else if symbol.val=1 then 1 else constants (symbol.val-2)
  | ⟨1,_⟩,_,arguments => -arguments 0
  | ⟨2,_⟩,symbol,arguments => if symbol.val=0 then arguments 0+arguments 1 else arguments 0*arguments 1
  | ⟨n+3,h⟩,_,_ => False.elim (by change n+3<3 at h; omega)

def relations : (n : Fin (bound+1)) → RelationSymbols n.val → (Fin n.val → K) → Prop
  | ⟨2,_⟩,_,arguments => arguments 0<arguments 1
  | _,_,_ => False

def value (constants : ℕ → K) (t : Term) (ρ : ℕ → K) : K := t.evaluate (functions constants) ρ
def Holds (constants : ℕ → K) (φ : Formula) (ρ : ℕ → K) : Prop :=
  φ.Holds (functions constants) relations ρ

variable (constants : ℕ → K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_var (name : ℕ) (ρ : ℕ → K) : value constants (var name) ρ=ρ name := rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_zero (ρ : ℕ → K) : value constants zero ρ=0 := rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_one (ρ : ℕ → K) : value constants one ρ=1 := rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_c (n : ℕ) (ρ : ℕ → K) : value constants (c n) ρ=constants n := by
  have h1 : n+2≠1 := by omega
  simp [value,c,functions,constantSymbol,NamedFiniteSyntax.Term.evaluate,h1]
omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_neg (t : Term) (ρ : ℕ → K) : value constants (neg t) ρ= -value constants t ρ := rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_add (s t : Term) (ρ : ℕ → K) :
    value constants (add s t) ρ=value constants s ρ+value constants t ρ := rfl
omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_mul (s t : Term) (ρ : ℕ → K) :
    value constants (mul s t) ρ=value constants s ρ*value constants t ρ := rfl

omit [IsStrictOrderedRing K] in
@[simp] theorem holds_equal (s t : Term) (ρ : ℕ → K) :
    Holds constants (.equal s t) ρ ↔ value constants s ρ=value constants t ρ := Iff.rfl
omit [IsStrictOrderedRing K] in
@[simp] theorem holds_lt (s t : Term) (ρ : ℕ → K) :
    Holds constants (lt s t) ρ ↔ value constants s ρ<value constants t ρ := Iff.rfl
omit [IsStrictOrderedRing K] in
@[simp] theorem holds_negation (φ : Formula) (ρ : ℕ → K) :
    Holds constants (negation φ) ρ ↔ ¬Holds constants φ ρ := Iff.rfl
omit [IsStrictOrderedRing K] in
@[simp] theorem holds_imp (φ ψ : Formula) (ρ : ℕ → K) :
    Holds constants (imp φ ψ) ρ ↔ (Holds constants φ ρ → Holds constants ψ ρ) := Iff.rfl
omit [IsStrictOrderedRing K] in
@[simp] theorem holds_all (name : ℕ) (φ : Formula) (ρ : ℕ → K) :
    Holds constants (all name φ) ρ ↔ ∀ x,Holds constants φ (Function.update ρ name x) := Iff.rfl
omit [IsStrictOrderedRing K] in
@[simp] theorem holds_conjunction (φ ψ : Formula) (ρ : ℕ → K) :
    Holds constants (conjunction φ ψ) ρ ↔ Holds constants φ ρ ∧ Holds constants ψ ρ := by
  simp only [conjunction,holds_negation,holds_imp]
  tauto
omit [IsStrictOrderedRing K] in
@[simp] theorem holds_disjunction (φ ψ : Formula) (ρ : ℕ → K) :
    Holds constants (disjunction φ ψ) ρ ↔ Holds constants φ ρ ∨ Holds constants ψ ρ := by
  simp only [disjunction,holds_negation,holds_imp]
  tauto
omit [IsStrictOrderedRing K] in
@[simp] theorem holds_existential (name : ℕ) (φ : Formula) (ρ : ℕ → K) :
    Holds constants (existential name φ) ρ ↔ ∃ x,Holds constants φ (Function.update ρ name x) := by
  classical
  simp [existential]

omit [IsStrictOrderedRing K] in
theorem close_valid (names : List ℕ) (φ : Formula)
    (h : ∀ ρ,Holds constants φ ρ) : ∀ ρ,Holds constants (close names φ) ρ := by
  induction names with
  | nil => exact h
  | cons name names ih =>
      intro ρ
      change ∀ x,Holds constants (close names φ) (Function.update ρ name x)
      exact fun x => ih (Function.update ρ name x)

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_positiveNatural (n : ℕ) (ρ : ℕ → K) :
    value constants (positiveNatural n) ρ=(n : K)+1 := by
  induction n with
  | zero => simp [positiveNatural]
  | succ n ih => simp only [positiveNatural,value_add,value_one,ih,Nat.cast_add,Nat.cast_one]

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_natural (n : ℕ) (ρ : ℕ → K) : value constants (natural n) ρ=(n : K) := by
  cases n with
  | zero => simp
  | succ n =>
      change value constants (if n+1=0 then zero else positiveNatural (n+1-1)) ρ=((n+1 : ℕ) : K)
      rw [ite_eq_right (Nat.succ_ne_zero n),Nat.add_sub_cancel,value_positiveNatural,
        Nat.cast_add,Nat.cast_one]

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] theorem value_integerTerm (n : ℕ) (ρ : ℕ → K) :
    value constants (integerTerm n) ρ=(Rationals.signed n : K) := by
  by_cases h : n%2=0
  · rw [integerTerm,ite_eq_left h,value_natural,Rationals.signed,ite_eq_left h]
    exact (Int.cast_natCast (R := K) (n/2)).symm
  · rw [integerTerm,ite_eq_right h,value_neg,value_natural,Rationals.signed,ite_eq_right h,Int.cast_neg]
    exact congrArg Neg.neg (Int.cast_natCast (R := K) (n/2+1)).symm

def hornerPolynomial (coefficients : List K) : K[X] :=
  coefficients.foldr (fun a previous => C a+X*previous) 0

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem eval_hornerPolynomial (coefficients : List K) (x : K) :
    (hornerPolynomial coefficients).eval x=
      coefficients.foldr (fun a previous => a+x*previous) 0 := by
  induction coefficients with
  | nil => simp [hornerPolynomial]
  | cons a coefficients ih =>
      change (C a+X*hornerPolynomial coefficients).eval x=
        a+x*coefficients.foldr (fun b previous => b+x*previous) 0
      rw [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,ih]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem hornerPolynomial_snoc (coefficients : List K) (a : K) (ha : a≠0) :
    hornerPolynomial (coefficients++[a])≠0 ∧
      (hornerPolynomial (coefficients++[a])).natDegree=coefficients.length := by
  induction coefficients with
  | nil => simp [hornerPolynomial,ha]
  | cons b coefficients ih =>
      have he : (hornerPolynomial ((b::coefficients)++[a])).natDegree=coefficients.length+1 := by
        change (C b+X*hornerPolynomial (coefficients++[a])).natDegree=_
        rw [natDegree_C_add,natDegree_X_mul ih.1,ih.2]
      refine ⟨?_,by simpa only [List.length_cons] using he⟩
      exact ne_zero_of_natDegree_gt (n := 0) (by rw [he]; omega)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem hornerPolynomial_range (ρ : ℕ → K) (degree : ℕ) (h : ρ degree≠0) :
    (hornerPolynomial ((List.range (degree+1)).map ρ)).natDegree=degree := by
  rw [List.range_succ,List.map_append,List.map_cons,List.map_nil]
  simpa only [List.length_map,List.length_range] using
    (hornerPolynomial_snoc ((List.range degree).map ρ) (ρ degree) h).2

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem value_hornerList (root : ℕ) (indices : List ℕ) (ρ : ℕ → K) :
    value constants (hornerList root indices) ρ=
      (indices.map ρ).foldr (fun a previous => a+ρ root*previous) 0 := by
  induction indices with
  | nil => simp [hornerList]
  | cons i indices ih =>
      change value constants (add (var i) (mul (var root) (hornerList root indices))) ρ=
        ρ i+ρ root*(indices.map ρ).foldr (fun a previous => a+ρ root*previous) 0
      rw [value_add,value_var,value_mul,value_var,ih]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem value_horner_update (degree : ℕ) (ρ : ℕ → K) (x : K) :
    value constants (horner degree (degree+1)) (Function.update ρ (degree+1) x)=
      (hornerPolynomial ((List.range (degree+1)).map ρ)).eval x := by
  rw [horner,value_hornerList,Function.update_self,eval_hornerPolynomial]
  have he : (List.range (degree+1)).map (Function.update ρ (degree+1) x)=
      (List.range (degree+1)).map ρ := by
    apply List.map_congr_left
    intro i hi
    exact Function.update_of_ne (by have := List.mem_range.mp hi; omega) _ _
  rw [he]

theorem finiteMatrix_valid (φ : Formula) (h : φ∈finiteMatrices) (ρ : ℕ → K) : Holds constants φ ρ := by
  simp only [finiteMatrices,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [holds_equal,holds_negation,holds_imp,holds_lt,holds_conjunction,
    holds_disjunction,holds_existential,value_add,value_mul,value_neg,value_var,value_zero,value_one]
  · exact add_assoc _ _ _
  · exact add_comm _ _
  · exact add_zero _
  · exact add_neg_cancel _
  · exact mul_assoc _ _ _
  · exact mul_comm _ _
  · exact mul_one _
  · exact mul_add _ _ _
  · exact zero_ne_one
  · intro hx
    refine ⟨(ρ 0)⁻¹,?_⟩
    simpa using mul_inv_cancel₀ hx
  · exact lt_irrefl _
  · exact fun h => lt_trans h.1 h.2
  · exact lt_trichotomy _ _
  · intro h
    simpa only [add_comm] using (_root_.add_lt_add_right h (ρ 2))
  · exact fun h => mul_pos h.1 h.2
  · exact zero_lt_one

omit [IsStrictOrderedRing K] in
theorem asymmetry_valid (ρ : ℕ → K) : Holds constants asymmetrySentence ρ := by
  simpa [asymmetrySentence,orderAsymmetry] using
    (show ∀ x y : K,x<y → ¬y<x from fun x y h => lt_asymm h)

variable [IsRealClosed K]

theorem positiveSquare_valid (ρ : ℕ → K) : Holds constants positiveSquare ρ := by
  have hs : ∀ x : K,0<x → ∃ y : K,y*y=x := by
    intro x hx
    obtain ⟨y,hy⟩ := (IsRealClosed.nonneg_iff_isSquare).mp hx.le
    exact ⟨y,hy.symm⟩
  simpa [positiveSquare] using hs

omit [IsStrictOrderedRing K] in
theorem oddBody_valid (degree : ℕ) (hdegree : Odd degree) (ρ : ℕ → K) :
    Holds constants (oddBody degree) ρ := by
  simp only [oddBody,holds_imp,holds_negation,holds_equal,value_var,value_zero,holds_existential]
  intro hleading
  let f := hornerPolynomial ((List.range (degree+1)).map ρ)
  have hf : Odd f.natDegree := by
    dsimp only [f]
    rw [hornerPolynomial_range ρ degree hleading]
    exact hdegree
  obtain ⟨x,hx⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hf
  refine ⟨x,?_⟩
  rw [value_horner_update]
  exact hx

omit [IsStrictOrderedRing K] in
theorem oddSentence_valid (n : ℕ) : ∀ ρ,Holds constants (oddSentence n) ρ :=
  close_valid constants (List.range (2*n+2)) (oddBody (2*n+1))
    (oddBody_valid constants (2*n+1) ⟨n,by omega⟩)

theorem finiteSentences_valid (φ : Formula) (h : φ∈finiteSentences) : ∀ ρ,Holds constants φ ρ := by
  change φ∈finiteMatrices.map (close [0,1,2])++[asymmetrySentence,positiveSquare] at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp h
    exact close_valid constants _ _ (finiteMatrix_valid constants ψ hψ)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · exact asymmetry_valid constants
    · exact positiveSquare_valid constants

def ValidCode (word : ℕ) : Prop := ∃ φ : Formula,formulaCode φ=word ∧ ∀ ρ,Holds constants φ ρ

theorem rcf_words_valid (word : ℕ) (h : word∈RCFAxiomWords) : ValidCode constants word := by
  rcases (rcf_generator_iff word).mp h with ⟨φ,hφ,hcode⟩ | ⟨n,rfl⟩
  · exact ⟨φ,hcode,finiteSentences_valid constants φ hφ⟩
  · exact ⟨oddSentence n,formulaCode_oddSentence n,oddSentence_valid constants n⟩

omit [IsRealClosed K] in
private theorem real_odd_root_of_leading_nonneg (f : ℝ[X]) (hodd : Odd f.natDegree)
    (hleading : 0≤f.leadingCoeff) : ∃ x : ℝ,f.IsRoot x := by
  by_contra! hnone
  have hpos : 0<f.eval 0 := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun y hy => False.elim (hnone y hy)) hleading
  have hneg := zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
    (P := f) (x := 0) (fun y hy => False.elim (hnone y hy)) hleading
  have he : (Int.negOnePow (f.natDegree : ℤ) : ℝ)= -1 := by
    simpa only [Int.cast_negOnePow_natCast] using (hodd.neg_one_pow : (-1 : ℝ)^f.natDegree= -1)
  rw [he,neg_one_mul] at hneg
  linarith

/-- This is derived from the existing real-polynomial IVT sign theorems. -/
theorem real_odd_root (f : ℝ[X]) (hodd : Odd f.natDegree) : ∃ x : ℝ,f.IsRoot x := by
  by_cases hleading : 0≤f.leadingCoeff
  · exact real_odd_root_of_leading_nonneg f hodd hleading
  · obtain ⟨x,hx⟩ := real_odd_root_of_leading_nonneg (-f)
      (by simpa only [natDegree_neg] using hodd) (by simpa only [leadingCoeff_neg] using neg_nonneg.mpr (le_of_not_ge hleading))
    refine ⟨x,?_⟩
    change (-f).eval x=0 at hx
    change f.eval x=0
    simpa only [Polynomial.eval_neg,neg_eq_zero] using hx

/-- Real closure is supplied locally in the semantic applications. -/
theorem realClosedReal : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField
    (fun {x} hx => ⟨Real.sqrt x,(Real.mul_self_sqrt hx).symm⟩)
    (fun {f} hf => real_odd_root f hf)

omit [IsRealClosed K] in
theorem belowSentence_holds (a : Point) (n j : ℕ) (ρ : ℕ → ℝ) :
    Holds (fun i => (a i : ℝ)) (belowSentence n j) ρ ↔ (Rationals.q j : ℝ)<(a n : ℝ) := by
  simp only [belowSentence,holds_lt,value_integerTerm,value_mul,value_natural,value_c]
  rw [StrictRational.rational_real,div_lt_iff₀ (by positivity)]
  exact Iff.of_eq (congrArg (fun x : ℝ => (Rationals.signed (Nat.unpair j).1 : ℝ)<x) (mul_comm _ _))

omit [IsRealClosed K] in
theorem aboveSentence_holds (a : Point) (n j : ℕ) (ρ : ℕ → ℝ) :
    Holds (fun i => (a i : ℝ)) (aboveSentence n j) ρ ↔ (a n : ℝ)<(Rationals.q j : ℝ) := by
  simp only [aboveSentence,holds_lt,value_integerTerm,value_mul,value_natural,value_c]
  rw [StrictRational.rational_real,lt_div_iff₀ (by positivity)]
  exact Iff.of_eq (congrArg (fun x : ℝ => x<(Rationals.signed (Nat.unpair j).1 : ℝ)) (mul_comm _ _))

theorem cut_words_valid (a : Point) (word : ℕ) (h : word∈cutAxioms a) :
    ValidCode (fun i => (a i : ℝ)) word := by
  rcases h with ⟨n,j,hj,rfl⟩ | ⟨n,j,hj,rfl⟩
  · exact ⟨belowSentence n j,formulaCode_belowSentence n j,
      fun ρ => (belowSentence_holds a n j ρ).mpr hj⟩
  · exact ⟨aboveSentence n j,formulaCode_aboveSentence n j,
      fun ρ => (aboveSentence_holds a n j ρ).mpr hj⟩

/-- Only T_a is interpreted here; a consistent extension is not assumed true in ℝ. -/
theorem theory_words_valid (a : Point) (word : ℕ) (h : word∈theoryAxioms a) :
    ValidCode (fun i => (a i : ℝ)) word := by
  let : IsRealClosed ℝ := realClosedReal
  exact h.elim (rcf_words_valid (fun i => (a i : ℝ)) word) (cut_words_valid a word)

theorem theory_formula_valid (a : Point) (φ : Formula) (h : formulaCode φ∈theoryAxioms a) :
    ∀ ρ,Holds (fun i => (a i : ℝ)) φ ρ := by
  obtain ⟨ψ,hψ,hvalid⟩ := theory_words_valid a (formulaCode φ) h
  have he : ψ=φ := NamedPostfixEncoding.formulaCode_injective hψ
  exact he ▸ hvalid

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms.Semantics
