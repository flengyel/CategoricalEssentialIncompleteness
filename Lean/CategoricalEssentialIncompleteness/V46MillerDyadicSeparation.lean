import CategoricalEssentialIncompleteness.V46MillerBinaryCore
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Finite dyadic certificates for separation of binary representations -/
noncomputable section
open scoped BigOperators
namespace CategoricalEssentialIncompleteness.V46.Miller

/-- The integer determined by the first k ordered binary digits. -/
def numeral (b : Bits) : ℕ → ℕ
  | 0 => 0
  | k+1 => 2 * numeral b k + (b k).val

theorem numeral_congr (b c : Bits) (k : ℕ) (h : ∀ j < k, b j = c j) :
    numeral b k = numeral c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [numeral, numeral, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

theorem numeral_partial_sum (b : Bits) (k : ℕ) :
    (∑ j ∈ Finset.range k, Real.ofDigitsTerm b j) = (numeral b k : ℝ) / (2 : ℝ)^k := by
  induction k with
  | zero => simp [numeral]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Real.ofDigitsTerm, numeral, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    field_simp

theorem numeral_bounds (b : Bits) (k : ℕ) :
    (numeral b k : ℝ) / (2 : ℝ)^k ≤ Real.ofDigits b ∧
      Real.ofDigits b ≤ ((numeral b k : ℝ)+1) / (2 : ℝ)^k := by
  have he := Real.ofDigits_eq_sum_add_ofDigits b k
  rw [numeral_partial_sum] at he
  have hn := Real.ofDigits_nonneg (fun i => b (i+k))
  have hl := Real.ofDigits_le_one (fun i => b (i+k))
  have hp : 0 ≤ ((2 : ℝ)^k)⁻¹ := by positivity
  have hmul := mul_nonneg hp hn
  have hle := mul_le_of_le_one_right hp hl
  constructor
  · linarith
  · rw [add_div, one_div]
    linarith

theorem numeral_separation (b c : Bits) (k : ℕ)
    (h : numeral b k + 1 < numeral c k) : Real.ofDigits b < Real.ofDigits c := by
  have hb := (numeral_bounds b k).2
  have hc := (numeral_bounds c k).1
  apply lt_of_le_of_lt hb
  apply lt_of_lt_of_le _ hc
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2^k)).mpr
  exact_mod_cast h

theorem exists_numeral_separation (b c : Bits) (h : Real.ofDigits b < Real.ofDigits c) :
    ∃ k, numeral b k + 1 < numeral c k := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < (Real.ofDigits c-Real.ofDigits b)/2 by linarith)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  rw [inv_pow] at hk
  have hb := (numeral_bounds b k).1
  have hc := (numeral_bounds c k).2
  rw [add_div,one_div] at hc
  have hh : ((numeral b k : ℝ)+1)/(2 : ℝ)^k < (numeral c k : ℝ)/(2 : ℝ)^k := by
    rw [add_div,one_div]
    linarith
  have hn := (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ)<2^k)).mp hh
  exact ⟨k,by exact_mod_cast hn⟩

def wordDigits (s : Word) (n : ℕ) : Bits := fun j => s[Nat.pair n j]?.getD 0

def wordNumeral (s : Word) (n k : ℕ) : ℕ := numeral (wordDigits s n) k

def Located (s : Word) (n k : ℕ) : Prop := ∀ j < k, Nat.pair n j < s.length

theorem wordNumeral_prefix (p : Bits) (N n k : ℕ)
    (h : ∀ j < k, Nat.pair n j < N) :
    wordNumeral (bitPrefix p N) n k = numeral (fun j => p (Nat.pair n j)) k := by
  apply numeral_congr
  intro j hj
  simp [wordDigits,bitPrefix,h j hj]

theorem wordNumeral_of_cylinder (p : Bits) (s : Word) (hp : p ∈ cylinder s)
    (n k : ℕ) (h : Located s n k) :
    wordNumeral s n k = numeral (fun j => p (Nat.pair n j)) k := by
  change bitPrefix p s.length = s at hp
  calc
    wordNumeral s n k = wordNumeral (bitPrefix p s.length) n k := congrArg (fun t => wordNumeral t n k) hp.symm
    _ = numeral (fun j => p (Nat.pair n j)) k := wordNumeral_prefix p s.length n k h

/-- Every queried position is below this computed finite bound. -/
def queryBound (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => max (queryBound n k) (Nat.pair n k + 1)

theorem query_lt_bound (n k j : ℕ) (hj : j < k) : Nat.pair n j < queryBound n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    change Nat.pair n j < max (queryBound n k) (Nat.pair n k+1)
    by_cases he : j=k
    · subst j
      exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
    · exact (ih (by omega)).trans_le (le_max_left _ _)

theorem located_prefix (p : Bits) (n k : ℕ) : Located (bitPrefix p (queryBound n k)) n k := by
  intro j hj
  simpa only [prefix_length] using query_lt_bound n k j hj

/-- A finite, rational dyadic certificate; its tests involve only integers. -/
def ApartAt (u s : Word) (n k : ℕ) : Prop :=
  Located u n k ∧ Located s n k ∧
    (wordNumeral u n k+1 < wordNumeral s n k ∨
      wordNumeral s n k+1 < wordNumeral u n k)

theorem apartAt_sound (u s : Word) (n k : ℕ) (h : ApartAt u s n k)
    (p q : Bits) (hp : p ∈ cylinder u) (hq : q ∈ cylinder s) : rho p ≠ rho q := by
  obtain ⟨hu,hs,h⟩ := h
  rw [wordNumeral_of_cylinder p u hp n k hu, wordNumeral_of_cylinder q s hq n k hs] at h
  have he : (rho p n : ℝ) ≠ (rho q n : ℝ) := by
    rcases h with h | h
    · exact (numeral_separation _ _ k h).ne
    · exact (numeral_separation _ _ k h).ne.symm
  intro hh
  exact he (congrArg (fun z : Point => (z n : ℝ)) hh)

theorem exists_apartAt (p q : Bits) (h : rho p ≠ rho q) :
    ∃ n k, ApartAt (bitPrefix p (queryBound n k)) (bitPrefix q (queryBound n k)) n k := by
  classical
  have hn : ∃ n, (rho p n : ℝ) ≠ (rho q n : ℝ) := by
    by_contra! hh
    apply h
    funext n
    exact Subtype.ext (hh n)
  obtain ⟨n,hn⟩ := hn
  rcases lt_or_gt_of_ne hn with hlt | hlt
  · obtain ⟨k,hk⟩ := exists_numeral_separation _ _ hlt
    refine ⟨n,k,located_prefix p n k,located_prefix q n k,Or.inl ?_⟩
    simpa only [wordNumeral_prefix p _ n k (query_lt_bound n k),
      wordNumeral_prefix q _ n k (query_lt_bound n k)] using hk
  · obtain ⟨k,hk⟩ := exists_numeral_separation _ _ hlt
    refine ⟨n,k,located_prefix p n k,located_prefix q n k,Or.inr ?_⟩
    simpa only [wordNumeral_prefix p _ n k (query_lt_bound n k),
      wordNumeral_prefix q _ n k (query_lt_bound n k)] using hk

theorem wordNumeral_append (u v : Word) (n k : ℕ) (h : Located u n k) :
    wordNumeral (u ++ v) n k = wordNumeral u n k := by
  apply numeral_congr
  intro j hj
  simp only [wordDigits, List.getElem?_append_left (h j hj)]

theorem apartAt_mono_left (u v s : Word) (n k : ℕ) (huv : u <+: v)
    (h : ApartAt u s n k) : ApartAt v s n k := by
  obtain ⟨t,rfl⟩ := huv
  obtain ⟨hu,hs,hc⟩ := h
  refine ⟨?_,hs,?_⟩
  · intro j hj
    have hh := hu j hj
    simp only [List.length_append]
    omega
  · simpa only [wordNumeral_append u t n k hu] using hc

theorem bitPrefix_isPrefix (p : Bits) {n m : ℕ} (h : n ≤ m) :
    bitPrefix p n <+: bitPrefix p m := by
  refine ⟨(bitPrefix p m).drop n, ?_⟩
  rw [← show (bitPrefix p m).take n = bitPrefix p n by
    rw [prefix_take,Nat.min_eq_left h]]
  exact List.take_append_drop _ _

end CategoricalEssentialIncompleteness.V46.Miller
