import CategoricalEssentialIncompleteness.V46MillerDyadicEffective
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Order

/-! # A concrete recursive rational enumeration for Miller real computations

The enumeration uses a signed numerator and a positive denominator, with
primitive-recursive numerical constructors. Outputs naming the same real
may differ between representations. This module does not assert a real
approximation program or the cut reduction.
-/
namespace CategoricalEssentialIncompleteness.V46.Miller.Rationals

def signed (k : ℕ) : ℤ :=
  if k % 2 = 0 then ((k / 2 : ℕ) : ℤ) else -((k / 2 + 1 : ℕ) : ℤ)

def integerCode : ℤ → ℕ
  | .ofNat n => 2*n
  | .negSucc n => 2*n+1

theorem signed_even (n : ℕ) : signed (2*n) = (n : ℤ) := by
  have hm : (2*n)%2=0 := by omega
  have hd : (2*n)/2=n := by omega
  simp only [signed,ite_eq_left hm,hd]

theorem signed_odd (n : ℕ) : signed (2*n+1) = -((n+1 : ℕ) : ℤ) := by
  have hm : (2*n+1)%2≠0 := by omega
  have hd : (2*n+1)/2=n := by omega
  simp only [signed,ite_eq_right hm,hd]

theorem signed_integerCode (z : ℤ) : signed (integerCode z)=z := by
  cases z with
  | ofNat n => exact signed_even n
  | negSucc n => simpa only [integerCode,Int.negSucc_eq,Int.natCast_succ] using signed_odd n

/-- Every index denotes a rational; denominator zero is excluded by construction. -/
def q (i : ℕ) : ℚ :=
  (signed (Nat.unpair i).1 : ℚ) / (((Nat.unpair i).2 + 1 : ℕ) : ℚ)

def rationalIndex (r : ℚ) : ℕ := Nat.pair (integerCode r.num) (r.den-1)

theorem q_rationalIndex (r : ℚ) : q (rationalIndex r)=r := by
  have hd : r.den-1+1=r.den := Nat.sub_add_cancel (Nat.succ_le_of_lt r.den_pos)
  simp only [q,rationalIndex,Nat.unpair_pair,signed_integerCode,hd]
  exact Rat.num_div_den r

theorem q_surjective : Function.Surjective q := fun r => ⟨rationalIndex r,q_rationalIndex r⟩

/-- An ordinary numerical output index for a nonnegative fraction. -/
def positiveIndex (a d : ℕ) : ℕ := Nat.pair (2*a) (d-1)

theorem q_positiveIndex (a d : ℕ) (hd : 0<d) :
    q (positiveIndex a d) = (a : ℚ)/(d : ℚ) := by
  have he : d-1+1=d := Nat.sub_add_cancel (Nat.succ_le_of_lt hd)
  simp only [q,positiveIndex,Nat.unpair_pair,signed_even,he,Int.cast_natCast]

theorem positiveIndex_primrec : Primrec₂ positiveIndex :=
  Primrec₂.natPair.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
    (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))

/-- A dyadic fraction does not require rational normalization to be output. -/
def dyadicIndex (a k : ℕ) : ℕ := positiveIndex a (2^k)

theorem q_dyadicIndex (a k : ℕ) :
    q (dyadicIndex a k) = (a : ℚ)/(2 : ℚ)^k := by
  rw [dyadicIndex,q_positiveIndex a (2^k) (by positivity)]
  simp only [Nat.cast_pow,Nat.cast_ofNat]

theorem dyadicIndex_primrec : Primrec₂ dyadicIndex := by
  have hp : Primrec₂ (fun a b : ℕ => a^b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact positiveIndex_primrec.comp Primrec.fst (hp.comp (Primrec.const 2) Primrec.snd)

theorem q_dyadicIndex_real (a k : ℕ) :
    ((q (dyadicIndex a k) : ℚ) : ℝ) = (a : ℝ)/(2 : ℝ)^k := by
  rw [q_dyadicIndex]
  push_cast
  rfl

end CategoricalEssentialIncompleteness.V46.Miller.Rationals
