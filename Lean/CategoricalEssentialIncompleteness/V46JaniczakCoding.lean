/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakLanguage

/-!
# Gödel codes for formulas with named variables

The constructor codes use natural-number pairing. Conjunction and quantification over finite blocks preserve primitive recursiveness, so the index of a finite class size determines its sentence effectively.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak.Formula

/-- Pairing the constructor tag with its arguments gives a Gödel number. -/
def code : Formula → ℕ
  | equal i j => Nat.pair 0 (Nat.pair i j)
  | related i j => Nat.pair 1 (Nat.pair i j)
  | top => Nat.pair 2 0
  | neg p => Nat.pair 3 p.code
  | conj p q => Nat.pair 4 (Nat.pair p.code q.code)
  | ex i p => Nat.pair 5 (Nat.pair i p.code)

theorem code_injective : Function.Injective code := by
  intro p
  induction p with
  | equal i j => intro q h; cases q <;> simp [code] at h ⊢; grind
  | related i j => intro q h; cases q <;> simp [code] at h ⊢; grind
  | top => intro q h; cases q <;> simp [code] at h ⊢
  | neg p ih => intro q h; cases q <;> simp [code] at h ⊢; grind
  | conj p q ih jh => intro r h; cases r <;> simp [code] at h ⊢; grind
  | ex i p ih => intro q h; cases q <;> simp [code] at h ⊢; grind

/-- A uniformly primitive recursive family of formula codes. -/
def Effective {α : Type*} [Primcodable α] (f : α → Formula) :=
  Primrec (fun a ↦ (f a).code)

namespace Effective

variable {α : Type*} [Primcodable α]

theorem const (p : Formula) : Effective (fun _ : α ↦ p) := Primrec.const p.code

theorem equal {i j : α → ℕ} (hi : Primrec i) (hj : Primrec j) :
    Effective (fun a ↦ Formula.equal (i a) (j a)) :=
  Primrec₂.natPair.comp (Primrec.const 0) (Primrec₂.natPair.comp hi hj)

theorem related {i j : α → ℕ} (hi : Primrec i) (hj : Primrec j) :
    Effective (fun a ↦ Formula.related (i a) (j a)) :=
  Primrec₂.natPair.comp (Primrec.const 1) (Primrec₂.natPair.comp hi hj)

theorem neg {f : α → Formula} (hf : Effective f) : Effective (fun a ↦ (f a).neg) :=
  Primrec₂.natPair.comp (Primrec.const 3) hf

theorem conj {f g : α → Formula} (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ Formula.conj (f a) (g a)) :=
  Primrec₂.natPair.comp (Primrec.const 4) (Primrec₂.natPair.comp hf hg)

theorem ex {i : α → ℕ} {f : α → Formula} (hi : Primrec i) (hf : Effective f) :
    Effective (fun a ↦ Formula.ex (i a) (f a)) :=
  Primrec₂.natPair.comp (Primrec.const 5) (Primrec₂.natPair.comp hi hf)

theorem imp {f g : α → Formula} (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ Formula.imp (f a) (g a)) := (hf.conj hg.neg).neg

theorem disj {f g : α → Formula} (hf : Effective f) (hg : Effective g) :
    Effective (fun a ↦ Formula.disj (f a) (g a)) := (hf.neg.conj hg.neg).neg

theorem all {i : α → ℕ} {f : α → Formula} (hi : Primrec i) (hf : Effective f) :
    Effective (fun a ↦ Formula.all (i a) (f a)) := (hf.neg.ex hi).neg

theorem conjBelow {f : α → ℕ → Formula} {n : α → ℕ}
    (hf : Effective (Function.uncurry f)) (hn : Primrec n) :
    Effective (fun a ↦ Formula.conjBelow (f a) (n a)) := by
  let step : α → ℕ × ℕ → ℕ := fun a j ↦ Nat.pair 4 (Nat.pair j.2 (f a j.1).code)
  have hs : Primrec₂ step := Primrec.to₂ <| Primrec₂.natPair.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.snd)
      (hf.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.nat_rec' hn (Primrec.const top.code) hs).of_eq fun a ↦ by
    dsimp only
    induction n a with
    | zero => rfl
    | succ j ih =>
      change Nat.pair _ (Nat.pair _ _) = Nat.pair _ (Nat.pair _ _)
      rw [ih]

theorem disjBelow {f : α → ℕ → Formula} {n : α → ℕ}
    (hf : Effective (Function.uncurry f)) (hn : Primrec n) :
    Effective (fun a ↦ Formula.disjBelow (f a) (n a)) := by
  let step : α → ℕ × ℕ → ℕ := fun a j ↦
    Nat.pair 3 (Nat.pair 4 (Nat.pair (Nat.pair 3 j.2) (Nat.pair 3 (f a j.1).code)))
  have part : Primrec fun y : α × (ℕ × ℕ) ↦ (f y.1 y.2.1).code :=
    hf.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have hs : Primrec₂ step := Primrec.to₂ <|
    Primrec₂.natPair.comp (Primrec.const 3) (Primrec₂.natPair.comp (Primrec.const 4)
      (Primrec₂.natPair.comp (Primrec₂.natPair.comp (Primrec.const 3) (Primrec.snd.comp Primrec.snd))
        (Primrec₂.natPair.comp (Primrec.const 3) part)))
  exact (Primrec.nat_rec' hn (Primrec.const (Formula.neg top).code) hs).of_eq fun a ↦ by
    dsimp only
    induction n a with
    | zero => rfl
    | succ j ih =>
      change Nat.pair _ (Nat.pair _ (Nat.pair (Nat.pair _ _) _)) = Nat.pair _ (Nat.pair _ (Nat.pair (Nat.pair _ _) _))
      rw [ih]
      rfl

theorem exBlock {a n : α → ℕ} {f : α → Formula}
    (ha : Primrec a) (hn : Primrec n) (hf : Effective f) :
    Effective (fun x ↦ Formula.exBlock (a x) (f x) (n x)) := by
  let step : α → ℕ × ℕ → ℕ := fun x j ↦ Nat.pair 5 (Nat.pair (a x+j.1) j.2)
  have hs : Primrec₂ step := Primrec.to₂ <| Primrec₂.natPair.comp (Primrec.const 5)
    (Primrec₂.natPair.comp
      (Primrec.nat_add.comp (ha.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
  exact (Primrec.nat_rec' hn hf hs).of_eq fun x ↦ by
    dsimp only
    induction n x with
    | zero => rfl
    | succ j ih =>
      change Nat.pair _ (Nat.pair _ _) = Nat.pair _ (Nat.pair _ _)
      rw [ih]

theorem distinctBelow {n : α → ℕ} (hn : Primrec n) :
    Effective (fun a ↦ Formula.distinctBelow (n a)) :=
  conjBelow (conjBelow ((equal Primrec.snd (Primrec.snd.comp Primrec.fst)).neg)
    Primrec.snd) hn

theorem exactly {n r : α → ℕ} (hn : Primrec n) (hr : Primrec r) :
    Effective (fun a ↦ Formula.exactly (n a) (r a)) :=
  exBlock (Primrec.const 0) hn <| (distinctBelow hn).conj <|
    (conjBelow (f := fun a j ↦ Formula.related (r a) j) (related (hr.comp Primrec.fst) Primrec.snd) hn).conj <|
    all hn <| (related hr hn).imp <|
      disjBelow (f := fun a j ↦ Formula.equal (n a) j) (equal (hn.comp Primrec.fst) Primrec.snd) hn

end Effective

theorem primrec_sizeSentence : Primrec (fun i ↦ (sizeSentence i).code) :=
  Effective.ex (Primrec.succ.comp Primrec.succ)
    (Effective.exactly Primrec.succ (Primrec.succ.comp Primrec.succ))

end Janiczak.Formula
