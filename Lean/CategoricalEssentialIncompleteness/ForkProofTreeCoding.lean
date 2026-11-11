/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkHilbertTrees

/-! # A recursive numerical coding of the exact finite proof-tree data -/

@[expose] public section

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.ProofTree

def encode : ProofTree → ℕ
  | .logical1 p q => 6*Nat.pair p.encode q.encode
  | .logical2 p q r => 6*Nat.pair p.encode (Nat.pair q.encode r.encode)+1
  | .logical3 p q => 6*Nat.pair p.encode q.encode+2
  | .positive x => 6*x+3
  | .negative x => 6*x+4
  | .mp t u => 6*Nat.pair t.encode u.encode+5

def decode (n : ℕ) : ProofTree :=
  if n%6=0 then .logical1 (Formula.decode (Nat.unpair (n/6)).1)
    (Formula.decode (Nat.unpair (n/6)).2)
  else if n%6=1 then .logical2 (Formula.decode (Nat.unpair (n/6)).1)
    (Formula.decode (Nat.unpair (Nat.unpair (n/6)).2).1)
    (Formula.decode (Nat.unpair (Nat.unpair (n/6)).2).2)
  else if n%6=2 then .logical3 (Formula.decode (Nat.unpair (n/6)).1)
    (Formula.decode (Nat.unpair (n/6)).2)
  else if n%6=3 then .positive (n/6)
  else if n%6=4 then .negative (n/6)
  else .mp (decode (Nat.unpair (n/6)).1) (decode (Nat.unpair (n/6)).2)
termination_by n
decreasing_by
  all_goals have hd : n/6<n := by omega
  · exact Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hd
  · exact Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hd

theorem encode_decode (n : ℕ) : encode (decode n)=n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [decode]
    split_ifs with h0 h1 h2 h3 h4
    · simp only [encode,Formula.encode_decode,Nat.pair_unpair]
      omega
    · simp only [encode,Formula.encode_decode,Nat.pair_unpair]
      omega
    · simp only [encode,Formula.encode_decode,Nat.pair_unpair]
      omega
    · change 6*(n/6)+3=n
      omega
    · change 6*(n/6)+4=n
      omega
    · change 6*Nat.pair (encode (decode (Nat.unpair (n/6)).1))
        (encode (decode (Nat.unpair (n/6)).2))+5=n
      have hd : n/6<n := by omega
      rw [ih _ (Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hd),
        ih _ (Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hd),Nat.pair_unpair]
      omega

theorem decode_encode (t : ProofTree) : decode (encode t)=t := by
  induction t with
  | logical1 p q =>
    rw [encode,decode]
    have hd : (6*Nat.pair p.encode q.encode)/6=Nat.pair p.encode q.encode := by omega
    rw [hd]
    simp only [Nat.mul_mod_right,ite_true,Nat.mul_div_right,Nat.unpair_pair,Formula.decode_encode]
  | logical2 p q r =>
    rw [encode,decode]
    have hd : (6*Nat.pair p.encode (Nat.pair q.encode r.encode)+1)/6=
        Nat.pair p.encode (Nat.pair q.encode r.encode) := by omega
    rw [hd]
    simp only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,Nat.reduceMod,
      Nat.reduceEqDiff,ite_false,ite_true,Nat.unpair_pair,Formula.decode_encode]
  | logical3 p q =>
    rw [encode,decode]
    have hd : (6*Nat.pair p.encode q.encode+2)/6=Nat.pair p.encode q.encode := by omega
    rw [hd]
    simp only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,Nat.reduceMod,
      Nat.reduceEqDiff,ite_false,ite_true,Nat.unpair_pair,Formula.decode_encode]
  | positive x =>
    rw [encode,decode]
    have hd : (6*x+3)/6=x := by omega
    rw [hd]
    simp only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,Nat.reduceMod,
      Nat.reduceEqDiff,ite_false,ite_true]
  | negative x =>
    rw [encode,decode]
    have hd : (6*x+4)/6=x := by omega
    rw [hd]
    simp only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,Nat.reduceMod,
      Nat.reduceEqDiff,ite_false,ite_true]
  | mp t u iht ihu =>
    rw [encode,decode]
    have hd : (6*Nat.pair t.encode u.encode+5)/6=Nat.pair t.encode u.encode := by omega
    rw [hd]
    simp only [Nat.add_mod,Nat.mul_mod_right,Nat.zero_add,Nat.reduceMod,
      Nat.reduceEqDiff,ite_false,Nat.unpair_pair,iht,ihu]

def codingEquiv : ProofTree ≃ ℕ := ⟨encode,decode,decode_encode,encode_decode⟩

instance : Primcodable ProofTree := Primcodable.ofEquiv ℕ codingEquiv

theorem encode_computable : Computable encode := Primrec.of_equiv.to_comp
theorem decode_computable : Computable decode := Primrec.of_equiv_symm.to_comp

/-- A node's conclusion is computable from its two computed child conclusions.
Invalid premise matching gives `none`. -/
def conclusion : ProofTree → Option Formula
  | .logical1 p q => some (H1 p q)
  | .logical2 p q r => some (H2 p q r)
  | .logical3 p q => some (H3 p q)
  | .positive x => some (.atom x)
  | .negative x => some (.neg (.atom x))
  | .mp t u => do
      let p ← conclusion t
      let q ← conclusion u
      match q with
      | .imp a b => if a=p then some b else none
      | _ => none

theorem concludes_conclusion {A B : Set ℕ} {t : ProofTree} {p : Formula}
    (h : Concludes A B t p) : t.conclusion=some p := by
  induction h with
  | logical1 | logical2 | logical3 | positive | negative => rfl
  | mp _ _ ih1 ih2 => simp [conclusion,ih1,ih2]

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.ProofTree
