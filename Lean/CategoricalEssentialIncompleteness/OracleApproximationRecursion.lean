/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleApproximation

/-! # Finite oracle approximations are closed under primitive recursion -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

def iteration (f g : ℕ → Part ℕ) (a : ℕ) : ℕ → Part ℕ
  | 0 => f a
  | n+1 => (iteration f g a n).bind (fun i => g (Nat.pair a (Nat.pair n i)))

def finiteIteration (F G : List ℕ × ℕ → Part ℕ) (l : List ℕ) (a n : ℕ) : Part ℕ :=
  iteration (fun x => F (l,x)) (fun x => G (l,x)) a n

theorem finiteIteration_partrec {F G : List ℕ × ℕ → Part ℕ} (hF : Partrec F) (hG : Partrec G) :
    Partrec (fun p : List ℕ × ℕ =>
      finiteIteration F G p.1 (Nat.unpair p.2).1 (Nat.unpair p.2).2) := by
  have hn : Computable (fun p : List ℕ × ℕ => (Nat.unpair p.2).2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  have ha : Computable (fun p : List ℕ × ℕ => (Nat.unpair p.2).1) :=
    Computable.fst.comp (Computable.unpair.comp Computable.snd)
  have hg : Partrec (fun p : List ℕ × ℕ => F (p.1,(Nat.unpair p.2).1)) :=
    hF.comp (Computable.pair Computable.fst ha)
  have hh : Partrec₂ (fun (p : List ℕ × ℕ) (q : ℕ × ℕ) =>
      G (p.1,Nat.pair (Nat.unpair p.2).1 (Nat.pair q.1 q.2))) :=
    (hG.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Primrec₂.natPair.to_comp.comp (ha.comp Computable.fst)
        (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
          (Computable.snd.comp Computable.snd))))).to₂
  apply (Partrec.nat_rec hn hg hh).of_eq
  intro p
  induction (Nat.unpair p.2).2 with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun k => k.bind (fun i => G (p.1,Nat.pair (Nat.unpair p.2).1
      (Nat.pair n i)))) ih

theorem finiteIteration_monotone {F G : List ℕ × ℕ → Part ℕ}
    (hF : MonotoneValues F) (hG : MonotoneValues G) (l l' : List ℕ) (hl : l <+: l')
    (a n y : ℕ) : y ∈ finiteIteration F G l a n → y ∈ finiteIteration F G l' a n := by
  induction n generalizing y with
  | zero => exact hF l l' hl a y
  | succ n ih =>
    intro hy
    obtain ⟨i,hi,hy⟩ := Part.mem_bind_iff.mp hy
    exact Part.mem_bind_iff.mpr ⟨i,ih i hi,hG l l' hl _ y hy⟩

theorem finiteIteration_represents {S : Set ℕ} {F G : List ℕ × ℕ → Part ℕ}
    {f g : ℕ → Part ℕ} (hMF : MonotoneValues F) (hMG : MonotoneValues G)
    (hf : Represents S F f) (hg : Represents S G g) (a n y : ℕ) :
    y ∈ iteration f g a n ↔ ∃ k,y ∈ finiteIteration F G (oraclePrefix S k) a n := by
  induction n generalizing y with
  | zero => exact hf a y
  | succ n ih =>
    constructor
    · intro hy
      obtain ⟨i,hi,hy⟩ := Part.mem_bind_iff.mp hy
      obtain ⟨k,hk⟩ := (ih i).mp hi
      obtain ⟨m,hm⟩ := (hg _ y).mp hy
      refine ⟨max k m,Part.mem_bind_iff.mpr ⟨i,?_,?_⟩⟩
      · exact finiteIteration_monotone hMF hMG _ _ (prefix_le S (le_max_left k m)) a n i hk
      · exact hMG _ _ (prefix_le S (le_max_right k m)) _ y hm
    · rintro ⟨k,hk⟩
      obtain ⟨i,hi,hy⟩ := Part.mem_bind_iff.mp hk
      exact Part.mem_bind_iff.mpr ⟨i,(ih i).mpr ⟨k,hi⟩,(hg _ y).mpr ⟨k,hy⟩⟩

theorem HasApproximation.prec {S : Set ℕ} {f g : ℕ → Part ℕ}
    (hf : HasApproximation S f) (hg : HasApproximation S g) :
    HasApproximation S (fun p => iteration f g (Nat.unpair p).1 (Nat.unpair p).2) := by
  obtain ⟨F,hF,hMF,hf⟩ := hf
  obtain ⟨G,hG,hMG,hg⟩ := hg
  exact ⟨_,finiteIteration_partrec hF hG,
    fun l l' hl x y => finiteIteration_monotone hMF hMG l l' hl _ _ y,
    fun x y => finiteIteration_represents hMF hMG hf hg _ _ y⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
