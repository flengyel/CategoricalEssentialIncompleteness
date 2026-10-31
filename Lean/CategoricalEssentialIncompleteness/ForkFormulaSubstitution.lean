/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ForkFormulaCoding
import Mathlib.Data.List.GetD

/-! # Recursive atom substitution on finite formula codes -/

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

namespace Formula

def sigma (f : ℕ → ℕ) (n : ℕ) : ℕ := encode (mapAtoms f (decode n))

theorem sigma_rec (f : ℕ → ℕ) (n : ℕ) :
    sigma f n=if n%3=0 then 3*f (n/3)
      else if n%3=1 then 3*sigma f (n/3)+1
      else 3*Nat.pair (sigma f (Nat.unpair (n/3)).1) (sigma f (Nat.unpair (n/3)).2)+2 := by
  unfold sigma
  rw [decode]
  split_ifs <;> rfl

def sigmaStep (f : ℕ → ℕ) (table : List ℕ) : ℕ :=
  if table.length%3=0 then 3*f (table.length/3)
  else if table.length%3=1 then 3*table.getD (table.length/3) 0+1
  else 3*Nat.pair (table.getD (Nat.unpair (table.length/3)).1 0)
    (table.getD (Nat.unpair (table.length/3)).2 0)+2

theorem computable_ite {α β : Type} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => if p x then f x else g x) :=
  (Computable.cond hp.decide.to_comp hf hg).of_eq (fun x => by by_cases h : p x <;> simp [h])

theorem sigmaStep_computable {f : ℕ → ℕ} (hf : Computable f) : Computable (sigmaStep f) := by
  have hl : Primrec (fun l : List ℕ => l.length) := Primrec.list_length
  have hd : Primrec (fun l : List ℕ => l.length/3) := Primrec.nat_div.comp hl (.const 3)
  have hm : Primrec (fun l : List ℕ => l.length%3) := Primrec.nat_mod.comp hl (.const 3)
  have h0 := (Primrec.eq.comp hm (.const 0))
  have h1 := (Primrec.eq.comp hm (.const 1))
  have hv : Primrec (fun l : List ℕ => l.getD (l.length/3) 0) :=
    (Primrec.list_getD 0).comp Primrec.id hd
  have hp : Primrec (fun l : List ℕ => Nat.pair
      (l.getD (Nat.unpair (l.length/3)).1 0) (l.getD (Nat.unpair (l.length/3)).2 0)) :=
    Primrec₂.natPair.comp
      ((Primrec.list_getD 0).comp Primrec.id (Primrec.fst.comp (Primrec.unpair.comp hd)))
      ((Primrec.list_getD 0).comp Primrec.id (Primrec.snd.comp (Primrec.unpair.comp hd)))
  exact computable_ite h0
    (Primrec.nat_mul.to_comp.comp (.const 3) (hf.comp hd.to_comp))
    (computable_ite h1
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 3) hv) (.const 1)).to_comp)
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 3) hp) (.const 2)).to_comp))

theorem sigmaStep_correct (f : ℕ → ℕ) (n : ℕ) :
    sigmaStep f ((List.range n).map (sigma f))=sigma f n := by
  have get (i : ℕ) (hi : i<n) :
      ((List.range n).map (sigma f)).getD i 0=sigma f i := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  unfold sigmaStep
  simp only [List.length_map,List.length_range]
  rw [sigma_rec f n]
  split_ifs with h0 h1
  · rfl
  · rw [get (n/3) (by omega)]
  · have hd : n/3<n := by omega
    rw [get _ (Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hd),
      get _ (Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hd)]

theorem sigma_computable {f : ℕ → ℕ} (hf : Computable f) : Computable (sigma f) := by
  have hg : Computable₂ (fun (_ : Unit) (table : List ℕ) => some (sigmaStep f table)) :=
    (Primrec.option_some.to_comp.comp ((sigmaStep_computable hf).comp Computable.snd)).to₂
  have h := Computable.nat_strong_rec (fun (_ : Unit) n => sigma f n) hg
    (fun _ n => congrArg some (sigmaStep_correct f n))
  exact h.comp (Computable.const ()) Computable.id

end Formula
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
