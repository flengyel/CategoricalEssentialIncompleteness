/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkProofTreeCoding
public import CategoricalEssentialIncompleteness.ForkFormulaSubstitution

/-! # Effective structural recursion on finite proof trees -/

@[expose] public section

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.ProofTree

variable {β : Type} [Primcodable β] [Inhabited β]

def fold (a1 : Formula × Formula → β) (a2 : Formula × Formula × Formula → β)
    (a3 : Formula × Formula → β) (pos neg : ℕ → β) (mp : β × β → β) : ProofTree → β
  | .logical1 p q => a1 (p,q)
  | .logical2 p q r => a2 (p,q,r)
  | .logical3 p q => a3 (p,q)
  | .positive x => pos x
  | .negative x => neg x
  | .mp t u => mp (fold a1 a2 a3 pos neg mp t,fold a1 a2 a3 pos neg mp u)

def foldStep (a1 : Formula × Formula → β) (a2 : Formula × Formula × Formula → β)
    (a3 : Formula × Formula → β) (pos neg : ℕ → β) (mp : β × β → β)
    (table : List β) : β :=
  let n := table.length
  let c := n/6
  if n%6=0 then a1 (Formula.decode (Nat.unpair c).1,Formula.decode (Nat.unpair c).2)
  else if n%6=1 then a2 (Formula.decode (Nat.unpair c).1,
    Formula.decode (Nat.unpair (Nat.unpair c).2).1,Formula.decode (Nat.unpair (Nat.unpair c).2).2)
  else if n%6=2 then a3 (Formula.decode (Nat.unpair c).1,Formula.decode (Nat.unpair c).2)
  else if n%6=3 then pos c
  else if n%6=4 then neg c
  else mp (table.getD (Nat.unpair c).1 default,table.getD (Nat.unpair c).2 default)

theorem foldStep_computable {a1 : Formula × Formula → β} {a2 : Formula × Formula × Formula → β}
    {a3 : Formula × Formula → β} {pos neg : ℕ → β} {mp : β × β → β}
    (h1 : Computable a1) (h2 : Computable a2) (h3 : Computable a3)
    (hp : Computable pos) (hn : Computable neg) (hm : Computable mp) :
    Computable (foldStep a1 a2 a3 pos neg mp) := by
  have hc : Primrec (fun table : List β => table.length/6) :=
    Primrec.nat_div.comp Primrec.list_length (.const 6)
  have ht : Primrec (fun table : List β => table.length%6) :=
    Primrec.nat_mod.comp Primrec.list_length (.const 6)
  have hl : Primrec (fun table : List β => (Nat.unpair (table.length/6)).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hc)
  have hr : Primrec (fun table : List β => (Nat.unpair (table.length/6)).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hc)
  have hpair : Computable (fun table : List β =>
      (Formula.decode (Nat.unpair (table.length/6)).1,Formula.decode (Nat.unpair (table.length/6)).2)) :=
    Computable.pair (Formula.decode_computable.comp hl.to_comp)
      (Formula.decode_computable.comp hr.to_comp)
  have htriple : Computable (fun table : List β =>
      (Formula.decode (Nat.unpair (table.length/6)).1,
        Formula.decode (Nat.unpair (Nat.unpair (table.length/6)).2).1,
        Formula.decode (Nat.unpair (Nat.unpair (table.length/6)).2).2)) :=
    Computable.pair (Formula.decode_computable.comp hl.to_comp)
      (Computable.pair
        (Formula.decode_computable.comp ((Primrec.fst.comp (Primrec.unpair.comp hr)).to_comp))
        (Formula.decode_computable.comp ((Primrec.snd.comp (Primrec.unpair.comp hr)).to_comp)))
  have hchildren : Computable (fun table : List β =>
      (table.getD (Nat.unpair (table.length/6)).1 default,
        table.getD (Nat.unpair (table.length/6)).2 default)) :=
    Computable.pair ((Primrec.list_getD default).comp Primrec.id hl).to_comp
      ((Primrec.list_getD default).comp Primrec.id hr).to_comp
  exact Formula.computable_ite (Primrec.eq.comp ht (.const 0)) (h1.comp hpair)
    (Formula.computable_ite (Primrec.eq.comp ht (.const 1)) (h2.comp htriple)
      (Formula.computable_ite (Primrec.eq.comp ht (.const 2)) (h3.comp hpair)
        (Formula.computable_ite (Primrec.eq.comp ht (.const 3)) (hp.comp hc.to_comp)
          (Formula.computable_ite (Primrec.eq.comp ht (.const 4)) (hn.comp hc.to_comp)
            (hm.comp hchildren)))))

theorem foldStep_correct (a1 : Formula × Formula → β) (a2 : Formula × Formula × Formula → β)
    (a3 : Formula × Formula → β) (pos neg : ℕ → β) (mp : β × β → β) (n : ℕ) :
    foldStep a1 a2 a3 pos neg mp
      ((List.range n).map (fun k => fold a1 a2 a3 pos neg mp (decode k)))=
      fold a1 a2 a3 pos neg mp (decode n) := by
  have get (i : ℕ) (hi : i<n) :
      ((List.range n).map (fun k => fold a1 a2 a3 pos neg mp (decode k))).getD i default=
        fold a1 a2 a3 pos neg mp (decode i) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  unfold foldStep
  simp only [List.length_map,List.length_range]
  rw [decode]
  split_ifs with h0 h1 h2 h3 h4
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have hd : n/6<n := by omega
    change mp (_,_)=mp (fold _ _ _ _ _ _ (decode (Nat.unpair (n/6)).1),
      fold _ _ _ _ _ _ (decode (Nat.unpair (n/6)).2))
    rw [get _ (Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hd),
      get _ (Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hd)]

theorem fold_computable {a1 : Formula × Formula → β} {a2 : Formula × Formula × Formula → β}
    {a3 : Formula × Formula → β} {pos neg : ℕ → β} {mp : β × β → β}
    (h1 : Computable a1) (h2 : Computable a2) (h3 : Computable a3)
    (hp : Computable pos) (hn : Computable neg) (hm : Computable mp) :
    Computable (fold a1 a2 a3 pos neg mp) := by
  have hg : Computable₂ (fun (_ : Unit) (table : List β) =>
      some (foldStep a1 a2 a3 pos neg mp table)) :=
    (Primrec.option_some.to_comp.comp
      ((foldStep_computable h1 h2 h3 hp hn hm).comp Computable.snd)).to₂
  have h := Computable.nat_strong_rec
    (fun (_ : Unit) n => fold a1 a2 a3 pos neg mp (decode n)) hg
    (fun _ n => congrArg some (foldStep_correct a1 a2 a3 pos neg mp n))
  have hc := (h.comp (Computable.const ()) Computable.id).comp encode_computable
  exact hc.of_eq (fun t => by simp only [id_eq,decode_encode])

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.ProofTree
