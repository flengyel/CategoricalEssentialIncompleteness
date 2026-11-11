/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkFormulaSubstitution
public import Mathlib.Computability.Partrec

/-! # Formula evaluation with partial recursive constructor operations

The operations may be undefined away from the chosen algebra carrier.
Correct recursive tables only query them on semantic values of formulas.
-/

@[expose] public section

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.Formula

def partialStep (atom neg imp : ℕ → Part ℕ) (table : List ℕ) : Part ℕ :=
  let n := table.length
  let c := n/3
  if n%3=0 then atom c
  else if n%3=1 then neg (table.getD c 0)
  else imp (Nat.pair (table.getD (Nat.unpair c).1 0) (table.getD (Nat.unpair c).2 0))

private theorem partrec_ite {α : Type} [Primcodable α] {p : α → Prop}
    [DecidablePred p] (hp : PrimrecPred p) {f g : α → Part ℕ}
    (hf : Partrec f) (hg : Partrec g) : Partrec (fun x => if p x then f x else g x) := by
  apply (Partrec.cond hp.decide.to_comp hf hg).of_eq
  intro x
  by_cases h : p x <;> simp [h]

theorem partialStep_partrec {atom neg imp : ℕ → Part ℕ}
    (ha : Partrec atom) (hn : Partrec neg) (hi : Partrec imp) :
    Partrec (partialStep atom neg imp) := by
  have hc : Primrec (fun t : List ℕ => t.length/3) :=
    Primrec.nat_div.comp Primrec.list_length (.const 3)
  have ht : Primrec (fun t : List ℕ => t.length%3) :=
    Primrec.nat_mod.comp Primrec.list_length (.const 3)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hc)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hc)
  exact partrec_ite (Primrec.eq.comp ht (.const 0)) (ha.comp hc.to_comp)
    (partrec_ite (Primrec.eq.comp ht (.const 1))
      (hn.comp (((Primrec.list_getD 0).comp Primrec.id hc).to_comp))
      (hi.comp (Primrec₂.natPair.comp
        ((Primrec.list_getD 0).comp Primrec.id hl)
        ((Primrec.list_getD 0).comp Primrec.id hr)).to_comp))

def partialTable (atom neg imp : ℕ → Part ℕ) : ℕ → Part (List ℕ)
  | 0 => Part.some []
  | n+1 => (partialTable atom neg imp n).bind fun t =>
      (partialStep atom neg imp t).map (fun y => t++[y])

theorem partialTable_partrec {atom neg imp : ℕ → Part ℕ}
    (ha : Partrec atom) (hn : Partrec neg) (hi : Partrec imp) :
    Partrec (partialTable atom neg imp) := by
  have hs : Partrec (fun t : List ℕ => (partialStep atom neg imp t).map (fun y => t++[y])) :=
    (partialStep_partrec ha hn hi).map
      ((Primrec.list_append.comp Primrec.fst
        (Primrec.list_cons.comp Primrec.snd (.const []))).to_comp.to₂)
  have hh : Partrec₂ (fun (_ : ℕ) (q : ℕ × List ℕ) =>
      (partialStep atom neg imp q.2).map (fun y => q.2++[y])) :=
    (hs.comp (Computable.snd.comp Computable.snd)).to₂
  apply (Partrec.nat_rec Computable.id (Partrec.const' (Part.some [])) hh).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun t : Part (List ℕ) =>
      t.bind fun l => (partialStep atom neg imp l).map (fun y => l++[y])) ih

theorem partialStep_correct (atom neg imp : ℕ → Part ℕ) (f : Formula → ℕ)
    (ha : ∀ x,f (.atom x) ∈ atom x)
    (hn : ∀ p,f (.neg p) ∈ neg (f p))
    (hi : ∀ p q,f (.imp p q) ∈ imp (Nat.pair (f p) (f q))) (n : ℕ) :
    f (decode n) ∈ partialStep atom neg imp ((List.range n).map (fun k => f (decode k))) := by
  have get (i : ℕ) (h : i<n) :
      ((List.range n).map (fun k => f (decode k))).getD i 0=f (decode i) := by
    rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  unfold partialStep
  simp only [List.length_map,List.length_range]
  rw [decode]
  split_ifs with h0 h1
  · exact ha _
  · have hd : n/3<n := by omega
    rw [get _ hd]
    exact hn _
  · have hd : n/3<n := by omega
    rw [get _ (Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hd),
      get _ (Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hd)]
    exact hi _ _

theorem partialTable_correct (atom neg imp : ℕ → Part ℕ) (f : Formula → ℕ)
    (ha : ∀ x,f (.atom x) ∈ atom x)
    (hn : ∀ p,f (.neg p) ∈ neg (f p))
    (hi : ∀ p q,f (.imp p q) ∈ imp (Nat.pair (f p) (f q))) (n : ℕ) :
    (List.range n).map (fun k => f (decode k)) ∈ partialTable atom neg imp n := by
  induction n with
  | zero => exact Part.mem_some _
  | succ n ih =>
    rw [partialTable,Part.mem_bind_iff]
    refine ⟨_,ih,?_⟩
    apply (Part.mem_map_iff _).mpr
    refine ⟨f (decode n),partialStep_correct atom neg imp f ha hn hi n,?_⟩
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil]

/-- A semantic formula fold is computable even when its constructor operations
are partial on ambient numerical codes. -/
theorem fold_computable_of_partial {atom neg imp : ℕ → Part ℕ}
    (ha : Partrec atom) (hn : Partrec neg) (hi : Partrec imp) (f : Formula → ℕ)
    (hfa : ∀ x,f (.atom x) ∈ atom x)
    (hfn : ∀ p,f (.neg p) ∈ neg (f p))
    (hfi : ∀ p q,f (.imp p q) ∈ imp (Nat.pair (f p) (f q))) : Computable f := by
  have ht : Partrec (fun n => partialTable atom neg imp (n+1)) :=
    (partialTable_partrec ha hn hi).comp Primrec.succ.to_comp
  have he : Partrec (fun n => (partialTable atom neg imp (n+1)).map (fun t => t.getD n 0)) :=
    ht.map (((Primrec.list_getD 0).comp Primrec.snd Primrec.fst).to_comp.to₂)
  have hc : Computable (fun n => f (decode n)) := he.of_eq_tot (fun n => by
    apply (Part.mem_map_iff _).mpr
    refine ⟨_,partialTable_correct atom neg imp f hfa hfn hfi (n+1),?_⟩
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp)
  exact (hc.comp encode_computable).of_eq (fun p => by rw [decode_encode])

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.Formula
