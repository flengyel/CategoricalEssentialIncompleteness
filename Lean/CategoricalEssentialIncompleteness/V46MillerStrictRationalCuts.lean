import CategoricalEssentialIncompleteness.V46MillerRationalCodes
import CategoricalEssentialIncompleteness.V46MillerUniformFinite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Uniform finite certificates for strict rational coordinate inequalities

The fixed rational enumeration has a signed numerator and a positive
denominator. The tests below use only natural-number arithmetic on those
codes and the integer specified by finitely many coordinate digits.
The resulting single oracle program works for every binary oracle.
-/
noncomputable section
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.StrictRational

/-- `q j` is strictly below the lower dyadic endpoint. -/
def belowTest (j number precision : ℕ) : Prop :=
  (Nat.unpair j).1 % 2 ≠ 0 ∨
    (Nat.unpair j).1 / 2 * 2^precision < number*((Nat.unpair j).2+1)

/-- The upper dyadic endpoint is strictly below `q j`. -/
def aboveTest (j number precision : ℕ) : Prop :=
  (Nat.unpair j).1 % 2 = 0 ∧
    (number+1)*((Nat.unpair j).2+1) < (Nat.unpair j).1 / 2 * 2^precision

theorem rational_real (j : ℕ) :
    (Rationals.q j : ℝ) = (Rationals.signed (Nat.unpair j).1 : ℝ) /
      (((Nat.unpair j).2+1 : ℕ) : ℝ) := by
  simp only [Rationals.q,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]

theorem belowTest_iff (j number precision : ℕ) :
    belowTest j number precision ↔
      (Rationals.q j : ℝ) < (number : ℝ)/(2 : ℝ)^precision := by
  rw [rational_real,div_lt_div_iff₀ (by positivity) (by positivity)]
  by_cases he : (Nat.unpair j).1 % 2=0
  · simp only [belowTest,Rationals.signed,he,ite_true,ne_eq,not_true_eq_false,false_or,Int.cast_natCast]
    exact_mod_cast (Iff.rfl :
      (Nat.unpair j).1 / 2 * 2^precision < number*((Nat.unpair j).2+1) ↔
      (Nat.unpair j).1 / 2 * 2^precision < number*((Nat.unpair j).2+1))
  · simp only [belowTest,Rationals.signed,he,ite_false,ne_eq,not_false_eq_true,true_or,Int.cast_neg,Int.cast_natCast]
    have hneg : -(((Nat.unpair j).1/2+1 : ℕ) : ℝ)*(2 : ℝ)^precision < 0 := by
      have hn : (0:ℝ)<(((Nat.unpair j).1/2+1:ℕ):ℝ) := by positivity
      have hp : (0:ℝ)<(2:ℝ)^precision := by positivity
      nlinarith [mul_pos hn hp]
    have hnonneg : (0 : ℝ) ≤ (number : ℝ)*(((Nat.unpair j).2+1 : ℕ) : ℝ) := by positivity
    exact ⟨fun _ => hneg.trans_le hnonneg,fun _ => trivial⟩

theorem aboveTest_iff (j number precision : ℕ) :
    aboveTest j number precision ↔
      ((number : ℝ)+1)/(2 : ℝ)^precision < (Rationals.q j : ℝ) := by
  rw [rational_real,div_lt_div_iff₀ (by positivity) (by positivity)]
  by_cases he : (Nat.unpair j).1 % 2=0
  · simp only [aboveTest,Rationals.signed,he,ite_true,true_and,Int.cast_natCast]
    exact_mod_cast (Iff.rfl :
      (number+1)*((Nat.unpair j).2+1) < (Nat.unpair j).1/2*2^precision ↔
      (number+1)*((Nat.unpair j).2+1) < (Nat.unpair j).1/2*2^precision)
  · simp only [aboveTest,Rationals.signed,he,ite_false,false_and,Int.cast_neg,Int.cast_natCast]
    have hpos : (0 : ℝ) < ((number : ℝ)+1)*(((Nat.unpair j).2+1 : ℕ) : ℝ) := by positivity
    have hneg : -(((Nat.unpair j).1/2+1 : ℕ) : ℝ)*(2 : ℝ)^precision < 0 := by
      have hn : (0:ℝ)<(((Nat.unpair j).1/2+1:ℕ):ℝ) := by positivity
      have hp : (0:ℝ)<(2:ℝ)^precision := by positivity
      nlinarith [mul_pos hn hp]
    constructor
    · exact False.elim
    · intro h
      linarith

theorem below_numeral_iff (b : Bits) (j : ℕ) :
    (Rationals.q j : ℝ) < Real.ofDigits b ↔ ∃ k,belowTest j (numeral b k) k := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < Real.ofDigits b-(Rationals.q j : ℝ) by linarith)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    rw [inv_pow] at hk
    have hb := (numeral_bounds b k).2
    rw [add_div,one_div] at hb
    refine ⟨k,(belowTest_iff j (numeral b k) k).mpr ?_⟩
    linarith
  · rintro ⟨k,hk⟩
    exact ((belowTest_iff j (numeral b k) k).mp hk).trans_le (numeral_bounds b k).1

theorem above_numeral_iff (b : Bits) (j : ℕ) :
    Real.ofDigits b < (Rationals.q j : ℝ) ↔ ∃ k,aboveTest j (numeral b k) k := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < (Rationals.q j : ℝ)-Real.ofDigits b by linarith)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    rw [inv_pow] at hk
    have hb := (numeral_bounds b k).1
    refine ⟨k,(aboveTest_iff j (numeral b k) k).mpr ?_⟩
    rw [add_div,one_div]
    linarith
  · rintro ⟨k,hk⟩
    exact (numeral_bounds b k).2.trans_lt ((aboveTest_iff j (numeral b k) k).mp hk)

/-- The Boolean selects `a(n)<q_j`; false selects `q_j<a(n)`. -/
def StrictSide (above : Bool) (a : Point) (input : ℕ × ℕ) : Prop :=
  if above then (a input.1 : ℝ) < (Rationals.q input.2 : ℝ)
    else (Rationals.q input.2 : ℝ) < (a input.1 : ℝ)

def Certificate (above : Bool) (input : ((Word × ℕ) × ℕ) × ℕ) : Prop :=
  Located input.1.1.1 input.1.1.2 input.2 ∧
    if above then aboveTest input.1.2 (wordNumeral input.1.1.1 input.1.1.2 input.2) input.2
      else belowTest input.1.2 (wordNumeral input.1.1.1 input.1.1.2 input.2) input.2

theorem certificate_primrec (above : Bool) : PrimrecPred (Certificate above) := by
  let A := ((Word × ℕ) × ℕ) × ℕ
  have harg : Primrec (fun x : A => (x.1.1,x.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hn := wordNumeral_primrec.comp harg
  have hl := located_primrec.comp harg
  have hj : Primrec (fun x : A => x.1.2) := Primrec.snd.comp Primrec.fst
  have ha : Primrec (fun x : A => (Nat.unpair x.1.2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hj)
  have hd : Primrec (fun x : A => (Nat.unpair x.1.2).2+1) :=
    Primrec.nat_add.comp (Primrec.snd.comp (Primrec.unpair.comp hj)) (Primrec.const 1)
  have hp : Primrec (fun x : A => 2^x.2) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.snd
  have he : PrimrecPred (fun x : A => (Nat.unpair x.1.2).1%2=0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp ha (Primrec.const 2)) (Primrec.const 0)
  have hleft := Primrec.nat_mul.comp (Primrec.nat_div.comp ha (Primrec.const 2)) hp
  cases above
  · exact hl.and (he.not.or (Primrec.nat_lt.comp hleft (Primrec.nat_mul.comp hn hd)))
  · exact hl.and (he.and (Primrec.nat_lt.comp
      (Primrec.nat_mul.comp (Primrec.nat_add.comp hn (Primrec.const 1)) hd) hleft))

theorem certificate_mono (above : Bool) {s t : Word} (hst : s <+: t) (n j k : ℕ)
    (h : Certificate above (((s,n),j),k)) : Certificate above (((t,n),j),k) := by
  obtain ⟨u,rfl⟩ := hst
  refine ⟨?_,?_⟩
  · intro m hm
    have hs : Nat.pair n m<s.length := h.1 m hm
    change Nat.pair n m<(s++u).length
    rw [List.length_append]
    omega
  · simpa only [wordNumeral_append s u n k h.1] using h.2

theorem certificate_prefix_iff (above : Bool) (p : Bits) (n j : ℕ) :
    StrictSide above (rho p) (n,j) ↔
      ∃ N k,Certificate above (((bitPrefix p N,n),j),k) := by
  cases above
  · change (Rationals.q j : ℝ) < Real.ofDigits (fun k => p (Nat.pair n k)) ↔ _
    rw [below_numeral_iff]
    constructor
    · rintro ⟨k,hk⟩
      refine ⟨queryBound n k,k,located_prefix p n k,?_⟩
      change belowTest j (wordNumeral (bitPrefix p (queryBound n k)) n k) k
      simpa only [wordNumeral_prefix p (queryBound n k) n k (query_lt_bound n k)] using hk
    · rintro ⟨N,k,hl,hk⟩
      refine ⟨k,?_⟩
      change belowTest j (wordNumeral (bitPrefix p N) n k) k at hk
      simpa only [wordNumeral_prefix p N n k (fun i hi => by
        simpa only [prefix_length] using hl i hi)] using hk
  · change Real.ofDigits (fun k => p (Nat.pair n k)) < (Rationals.q j : ℝ) ↔ _
    rw [above_numeral_iff]
    constructor
    · rintro ⟨k,hk⟩
      refine ⟨queryBound n k,k,located_prefix p n k,?_⟩
      change aboveTest j (wordNumeral (bitPrefix p (queryBound n k)) n k) k
      simpa only [wordNumeral_prefix p (queryBound n k) n k (query_lt_bound n k)] using hk
    · rintro ⟨N,k,hl,hk⟩
      refine ⟨k,?_⟩
      change aboveTest j (wordNumeral (bitPrefix p N) n k) k at hk
      simpa only [wordNumeral_prefix p N n k (fun i hi => by
        simpa only [prefix_length] using hl i hi)] using hk

/-- One ordinary predicate, independent of the represented point. -/
def tableCertificate (above : Bool) (input : (ℕ × ℕ) × List ℕ) : Prop :=
  ∃ k,Certificate above (((normalizeWord input.2,input.1.1),input.1.2),k)

theorem tableCertificate_re (above : Bool) : REPred (tableCertificate above) := by
  have ha : Computable (fun x : ((ℕ × ℕ) × List ℕ) × ℕ =>
      (((normalizeWord x.1.2,x.1.1.1),x.1.1.2),x.2)) :=
    Computable.pair (Computable.pair
      (Computable.pair (normalizeWord_primrec.to_comp.comp (Computable.snd.comp Computable.fst))
        (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      (Computable.snd.comp (Computable.fst.comp Computable.fst))) Computable.snd
  exact (REPred.comp ha (certificate_primrec above).computablePred.to_re).projection

theorem tableCertificate_mono (above : Bool) (n j : ℕ) {s t : List ℕ} (hst : s <+: t)
    (h : tableCertificate above ((n,j),s)) : tableCertificate above ((n,j),t) := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k,certificate_mono above (normalizeWord_prefix s t hst) n j k hk⟩

theorem tableCertificate_prefix_iff (above : Bool) (p : Bits) (n j : ℕ) :
    StrictSide above (rho p) (n,j) ↔
      ∃ N,tableCertificate above ((n,j),OracleProgram.numericalPrefix p N) := by
  simpa only [tableCertificate,OracleProgram.numericalPrefix,normalizeWord_numericalPrefix] using
    certificate_prefix_iff above p n j

theorem strictSide_enumerable (above : Bool) (a : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint a) (StrictSide above a) := by
  refine ⟨tableCertificate above,tableCertificate_re above,?_,?_⟩
  · intro x s t hst h
    exact tableCertificate_mono above x.1 x.2 hst h
  · intro p hp x
    have he : rho p=a := hp
    exact (show StrictSide above a x ↔ StrictSide above (rho p) x from by rw [he]).trans
      (tableCertificate_prefix_iff above p x.1 x.2)

theorem rational_below_enumerable (a : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint a)
      (fun x : ℕ × ℕ => (Rationals.q x.2 : ℝ) < (a x.1 : ℝ)) :=
  strictSide_enumerable false a

theorem rational_above_enumerable (a : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint a)
      (fun x : ℕ × ℕ => (a x.1 : ℝ) < (Rationals.q x.2 : ℝ)) :=
  strictSide_enumerable true a

theorem negative_below (a : Point) (n j : ℕ) (hj : (Rationals.q j : ℝ)<0) :
    StrictSide false a (n,j) := hj.trans_le (a n).property.1

theorem beyond_one_above (a : Point) (n j : ℕ) (hj : 1<(Rationals.q j : ℝ)) :
    StrictSide true a (n,j) := (a n).property.2.trans_lt hj

theorem not_above_zero (a : Point) (n : ℕ) :
    ¬StrictSide true a (n,Rationals.dyadicIndex 0 0) := by
  change ¬(a n : ℝ)<(Rationals.q (Rationals.dyadicIndex 0 0) : ℝ)
  rw [Rationals.q_dyadicIndex_real]
  simpa only [Nat.cast_zero,pow_zero,zero_div] using not_lt.mpr (a n).property.1

theorem not_below_one (a : Point) (n : ℕ) :
    ¬StrictSide false a (n,Rationals.dyadicIndex 1 0) := by
  change ¬(Rationals.q (Rationals.dyadicIndex 1 0) : ℝ)<(a n : ℝ)
  rw [Rationals.q_dyadicIndex_real]
  simpa only [Nat.cast_one,pow_zero,div_one] using not_lt.mpr (a n).property.2

/-- The index is chosen before every oracle, coordinate, and rational index.
The full output graph also asserts undefinedness when strictness fails. -/
theorem exists_program (above : Bool) : ∃ d : ℕ,∀ p : Bits,∀ n j value : ℕ,
    value ∈ OracleProgram.numberedEval d p (Nat.pair n j) ↔
      StrictSide above (rho p) (n,j) ∧ value=0 := by
  let T : (List ℕ × ℕ) × ℕ → Prop := fun x =>
    tableCertificate above (Nat.unpair x.1.2,x.1.1) ∧ x.2=0
  have hT : REPred T :=
    (REPred.comp (Computable.pair
      (Computable.unpair.comp (Computable.snd.comp Computable.fst))
      (Computable.fst.comp Computable.fst)) (tableCertificate_re above)).and
      ((Primrec.eq.comp Primrec.snd (Primrec.const 0)).computablePred.to_re)
  have hu : ∀ a x y,T (a,x) → T (a,y) → x=y := by
    intro a x y hx hy
    exact hx.2.trans hy.2.symm
  obtain ⟨F,hF,hgraph⟩ := FiniteSemidecision.functional_graph hT hu
  have hm : OracleComputation.MonotoneValues F := by
    intro s t hst input value hv
    obtain ⟨hc,he⟩ := (hgraph (s,input) value).mp hv
    exact (hgraph (t,input) value).mpr
      ⟨tableCertificate_mono above (Nat.unpair input).1 (Nat.unpair input).2 hst hc,he⟩
  obtain ⟨d,hd⟩ := OracleProgram.exists_uniform_index F hF hm
  refine ⟨d,?_⟩
  intro p n j value
  rw [hd]
  constructor
  · rintro ⟨N,hN⟩
    obtain ⟨hc,he⟩ := (hgraph (OracleProgram.numericalPrefix p N,Nat.pair n j) value).mp hN
    exact ⟨(tableCertificate_prefix_iff above p n j).mpr
      ⟨N,by simpa only [Nat.unpair_pair] using hc⟩,he⟩
  · rintro ⟨hc,he⟩
    obtain ⟨N,hN⟩ := (tableCertificate_prefix_iff above p n j).mp hc
    refine ⟨N,(hgraph (OracleProgram.numericalPrefix p N,Nat.pair n j) value).mpr ?_⟩
    exact ⟨by simpa only [Nat.unpair_pair] using hN,he⟩

theorem exists_program_on_representations (above : Bool) :
    ∃ d : ℕ,∀ a : Point,∀ p∈representations a,∀ n j value : ℕ,
      value ∈ OracleProgram.numberedEval d p (Nat.pair n j) ↔
        StrictSide above a (n,j) ∧ value=0 := by
  obtain ⟨d,hd⟩ := exists_program above
  refine ⟨d,?_⟩
  intro a p hp n j value
  have he : rho p=a := hp
  simpa only [he] using hd p n j value

end CategoricalEssentialIncompleteness.V46.Miller.StrictRational
