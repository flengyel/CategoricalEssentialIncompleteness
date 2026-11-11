/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRecursionComparison

/-! # Oracle recursion computes finite oracle prefixes -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

open Encodable

theorem recursiveIn_of_computable {S : Set ℕ} {f : ℕ → ℕ} (hf : Computable f) :
    Nat.RecursiveIn (oracleSet S) (fun n => Part.some (f n)) :=
  (Partrec.nat_iff.mp hf.partrec).recursiveIn

def appendCode (p : ℕ) : ℕ :=
  encode (((decode (α := List ℕ) (Nat.unpair p).1).getD []) ++ [(Nat.unpair p).2])

theorem appendCode_computable : Computable appendCode := by
  have hp := Computable.unpair
  have hl : Computable (fun p : ℕ =>
      (decode (α := List ℕ) (Nat.unpair p).1).getD []) :=
    Computable.option_getD (Computable.decode.comp (Computable.fst.comp hp)) (Computable.const [])
  exact Computable.encode.comp (Primrec.list_append.to_comp.comp hl
    (Primrec.list_cons.to_comp.comp (Computable.snd.comp hp) (Computable.const [])))

def prefixStep (S : Set ℕ) (p : ℕ) : ℕ :=
  appendCode (Nat.pair (Nat.unpair (Nat.unpair p).2).2
    (answer S (Nat.unpair (Nat.unpair p).2).1))

theorem prefixStep_recursiveIn (S : Set ℕ) :
    Nat.RecursiveIn (oracleSet S) (fun p => Part.some (prefixStep S p)) := by
  have hq : Nat.RecursiveIn (oracleSet S) (oracleFunction S) :=
    .oracle _ (Set.mem_singleton _)
  have hn : Computable (fun p : ℕ => (Nat.unpair (Nat.unpair p).2).1) :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have ha : Computable (fun p : ℕ => (Nat.unpair (Nat.unpair p).2).2) :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  refine (Nat.RecursiveIn.comp (recursiveIn_of_computable appendCode_computable)
    (.pair (recursiveIn_of_computable ha) (.comp hq (recursiveIn_of_computable hn)))).of_eq ?_
  intro p
  simp [prefixStep,oracleFunction,Seq.seq,Part.bind_eq_bind]

def prefixRec (S : Set ℕ) (p : ℕ) : Part ℕ :=
  let (a,n) := Nat.unpair p
  n.rec (Part.some (encode ([] : List ℕ))) (fun k ih => ih.bind fun i =>
    Part.some (prefixStep S (Nat.pair a (Nat.pair k i))))

theorem prefixRec_recursiveIn (S : Set ℕ) : Nat.RecursiveIn (oracleSet S) (prefixRec S) :=
  .prec (recursiveIn_of_computable (Computable.const (encode ([] : List ℕ))))
    (prefixStep_recursiveIn S)

theorem prefixRec_succ (S : Set ℕ) (a n : ℕ) :
    prefixRec S (Nat.pair a (n+1))=(prefixRec S (Nat.pair a n)).bind
      (fun i => Part.some (prefixStep S (Nat.pair a (Nat.pair n i)))) := by
  simp only [prefixRec,Nat.unpair_pair]

theorem prefixRec_eq (S : Set ℕ) (a n : ℕ) :
    prefixRec S (Nat.pair a n)=Part.some (encode (oraclePrefix S n)) := by
  induction n with
  | zero => simp [prefixRec,Nat.unpair_pair,oraclePrefix]
  | succ n ih =>
    rw [prefixRec_succ,ih,Part.bind_some]
    simp only [prefixStep,Nat.unpair_pair,appendCode,Encodable.encodek,Option.getD_some]
    congr 2
    simp [oraclePrefix,List.range_succ,List.map_append]

/-- The construction queries exactly the finitely many characteristic-oracle
answers needed for the prefix and returns its ordinary numerical list code. -/
theorem prefixCode_recursiveIn (S : Set ℕ) :
    Nat.RecursiveIn (oracleSet S) (fun n => Part.some (encode (oraclePrefix S n))) := by
  have hp : Computable (fun n : ℕ => Nat.pair 0 n) :=
    Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id
  exact (Nat.RecursiveIn.comp (prefixRec_recursiveIn S) (recursiveIn_of_computable hp)).of_eq
    (fun n => by simpa only [Part.bind_eq_bind,Part.bind_some] using prefixRec_eq S 0 n)

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
