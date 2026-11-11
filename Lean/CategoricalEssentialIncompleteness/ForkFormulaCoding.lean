/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Foundation.Vorspiel.Computability

/-! # Exact finite syntax for the three-point application -/

@[expose] public section

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

inductive Formula where
  | atom : ℕ → Formula
  | neg : Formula → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq

namespace Formula

def encode : Formula → ℕ
  | atom x => 3*x
  | neg p => 3*encode p+1
  | imp p q => 3*Nat.pair (encode p) (encode q)+2

def decode (n : ℕ) : Formula :=
  if n%3=0 then atom (n/3)
  else if n%3=1 then neg (decode (n/3))
  else imp (decode (Nat.unpair (n/3)).1) (decode (Nat.unpair (n/3)).2)
termination_by n
decreasing_by
  all_goals have hd : n/3<n := by omega
  · exact hd
  · exact Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hd
  · exact Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hd

theorem encode_decode (n : ℕ) : encode (decode n)=n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [decode]
    split_ifs with h0 h1
    · change 3*(n/3)=n
      omega
    · change 3*encode (decode (n/3))+1=n
      rw [ih (n/3) (by omega)]
      omega
    · change 3*Nat.pair (encode (decode (Nat.unpair (n/3)).1))
        (encode (decode (Nat.unpair (n/3)).2))+2=n
      have hd : n/3<n := by omega
      rw [ih _ (Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hd),
        ih _ (Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hd),Nat.pair_unpair]
      omega

theorem decode_encode (p : Formula) : decode (encode p)=p := by
  induction p with
  | atom x => rw [encode,decode]; simp
  | neg p ih =>
    rw [encode,decode]
    have hd : (3*encode p+1)/3=encode p := by omega
    rw [hd]
    simpa only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,Nat.reduceMod,
      Nat.one_ne_zero,if_false,if_true,Nat.add_div,Nat.mul_div_right,Nat.reduceDiv,
      Nat.add_zero] using congrArg neg ih
  | imp p q ihp ihq =>
    rw [encode,decode]
    have hd : (3*Nat.pair (encode p) (encode q)+2)/3=Nat.pair (encode p) (encode q) := by omega
    rw [hd]
    simp only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,Nat.reduceMod,
      Nat.reduceEqDiff,if_false,Nat.add_div,Nat.mul_div_right,Nat.reduceDiv,
      Nat.add_zero,Nat.unpair_pair,ihp,ihq]

def codingEquiv : Formula ≃ ℕ := ⟨encode,decode,decode_encode,encode_decode⟩

instance : Primcodable Formula := Primcodable.ofEquiv ℕ codingEquiv

theorem encode_computable : Computable encode := Primrec.of_equiv.to_comp
theorem decode_computable : Computable decode := Primrec.of_equiv_symm.to_comp

def mapAtoms (f : ℕ → ℕ) : Formula → Formula
  | atom x => atom (f x)
  | neg p => neg (mapAtoms f p)
  | imp p q => imp (mapAtoms f p) (mapAtoms f q)

@[simp] theorem mapAtoms_id (p : Formula) : mapAtoms id p=p := by
  induction p <;> simp [mapAtoms, *]

theorem mapAtoms_comp (f g : ℕ → ℕ) (p : Formula) :
    mapAtoms g (mapAtoms f p)=mapAtoms (g ∘ f) p := by
  induction p <;> simp [mapAtoms, *]

def eval (v : ℕ → Prop) : Formula → Prop
  | atom x => v x
  | neg p => ¬ eval v p
  | imp p q => eval v p → eval v q

theorem eval_mapAtoms (v f) (p : Formula) : eval v (mapAtoms f p)=eval (v ∘ f) p := by
  induction p <;> simp [mapAtoms,eval, *]

end Formula
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
