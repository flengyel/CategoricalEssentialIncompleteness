/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Computability.RE
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Tauto

/-!
# The language and axioms of Janiczak's equivalence-relation theory

The only nonlogical symbol is a binary relation. Natural numbers name variables.
The formulas have equality, conjunction, negation and existential quantification.
An axiom with free variables denotes its universal closure.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak

inductive Formula where
  | equal (x y : ℕ)
  | related (x y : ℕ)
  | top
  | neg (p : Formula)
  | conj (p q : Formula)
  | ex (x : ℕ) (p : Formula)
  deriving DecidableEq

namespace Formula

def imp (p q : Formula) := neg (conj p (neg q))
def disj (p q : Formula) := neg (conj (neg p) (neg q))
def all (x : ℕ) (p : Formula) := neg (ex x (neg p))

def Holds {X : Type*} (E : X → X → Prop) (v : ℕ → X) : Formula → Prop
  | equal x y => v x = v y
  | related x y => E (v x) (v y)
  | top => True
  | neg p => ¬ p.Holds E v
  | conj p q => p.Holds E v ∧ q.Holds E v
  | ex x p => ∃ a, p.Holds E (Function.update v x a)

@[simp] theorem holds_imp {X : Type*} (E : X → X → Prop) (v : ℕ → X) (p q : Formula) :
    (imp p q).Holds E v ↔ (p.Holds E v → q.Holds E v) := by
  classical
  simp [imp, Holds]

@[simp] theorem holds_disj {X : Type*} (E : X → X → Prop) (v : ℕ → X) (p q : Formula) :
    (disj p q).Holds E v ↔ p.Holds E v ∨ q.Holds E v := by
  classical
  change (¬ (¬ p.Holds E v ∧ ¬ q.Holds E v)) ↔ _
  tauto

@[simp] theorem holds_all {X : Type*} (E : X → X → Prop) (v : ℕ → X) (x : ℕ) (p : Formula) :
    (all x p).Holds E v ↔ ∀ a, p.Holds E (Function.update v x a) := by
  classical
  simp [all, Holds]

def conjBelow (p : ℕ → Formula) : ℕ → Formula
  | 0 => top
  | n + 1 => conj (conjBelow p n) (p n)

def disjBelow (p : ℕ → Formula) : ℕ → Formula
  | 0 => neg top
  | n + 1 => disj (disjBelow p n) (p n)

def exBlock (a : ℕ) (p : Formula) : ℕ → Formula
  | 0 => p
  | n + 1 => ex (a+n) (exBlock a p n)

@[simp] theorem holds_conjBelow {X : Type*} (E : X → X → Prop) (v : ℕ → X)
    (p : ℕ → Formula) (n : ℕ) :
    (conjBelow p n).Holds E v ↔ ∀ j < n, (p j).Holds E v := by
  induction n with
  | zero => simp [conjBelow, Holds]
  | succ n ih => simp only [conjBelow, Holds, ih, Nat.forall_lt_succ_right]

@[simp] theorem holds_disjBelow {X : Type*} (E : X → X → Prop) (v : ℕ → X)
    (p : ℕ → Formula) (n : ℕ) :
    (disjBelow p n).Holds E v ↔ ∃ j < n, (p j).Holds E v := by
  induction n with
  | zero => simp [disjBelow, Holds]
  | succ n ih => simp only [disjBelow, holds_disj, ih, Nat.exists_lt_succ_right]

theorem holds_exBlock {X : Type*} (E : X → X → Prop) (p : Formula) (a n : ℕ)
    (v : ℕ → X) :
    (exBlock a p n).Holds E v ↔
      ∃ w : ℕ → X, (∀ j, (j < a ∨ a+n ≤ j) → w j = v j) ∧ p.Holds E w := by
  induction n generalizing v with
  | zero =>
    simp only [exBlock, Nat.add_zero]
    constructor
    · exact fun h ↦ ⟨v, fun _ _ ↦ rfl, h⟩
    · rintro ⟨w, he, hw⟩
      have : w = v := funext fun j ↦ he j (by omega)
      simpa [this] using hw
  | succ n ih =>
    simp only [exBlock, Holds, ih]
    constructor
    · rintro ⟨b, w, he, hw⟩
      refine ⟨w, ?_, hw⟩
      intro j hj
      rw [he j (by omega), Function.update_of_ne (by omega : j ≠ a+n)]
    · rintro ⟨w, he, hw⟩
      refine ⟨w (a+n), w, ?_, hw⟩
      intro j hj
      by_cases h : j = a+n
      · simp [h]
      · rw [Function.update_of_ne h, he j (by omega)]

/-- The variables below `n` are pairwise distinct. -/
def distinctBelow (n : ℕ) :=
  conjBelow (fun j ↦ conjBelow (fun i ↦ neg (equal i j)) j) n

/-- A class with representative `x` has at least `n` elements. Its bound variables are below `n`. -/
def atLeast (n x : ℕ) :=
  exBlock 0 (conj (distinctBelow n) (conjBelow (related x) n)) n

/-- A class with representative `x` has precisely `n` elements. The index `x` must exceed `n`. -/
def exactly (n x : ℕ) :=
  exBlock 0 (conj (distinctBelow n) (conj (conjBelow (related x) n)
    (all n (imp (related x n) (disjBelow (equal n) n))))) n

/-- The sentence denoted by `Aᵢ` in Murwanashyaka, Pakhomov and Visser. -/
def sizeSentence (i : ℕ) := ex (i+2) (exactly (i+1) (i+2))

/-- At most one class has size `n`. -/
def uniqueSize (n : ℕ) :=
  all (n+1) (all (n+2)
    (imp (conj (exactly n (n+1)) (exactly n (n+2))) (related (n+1) (n+2))))

/-- There are at least `n` distinct classes, each with at least `n` elements. -/
def manyLarge (n : ℕ) :=
  exBlock (n+1) (conj
    (conjBelow (fun j ↦ conjBelow (fun i ↦ neg (related (n+1+i) (n+1+j))) j) n)
    (conjBelow (fun i ↦ atLeast n (n+1+i)) n)) n

def reflSentence := all 0 (related 0 0)
def symmSentence := all 0 (all 1 (imp (related 0 1) (related 1 0)))
def transSentence := all 0 (all 1 (all 2
  (imp (conj (related 0 1) (related 1 2)) (related 0 2))))

end Formula

open Formula

inductive Jan : Set Formula
  | refl : Jan reflSentence
  | symm : Jan symmSentence
  | trans : Jan transSentence
  | uniqueSize (n : ℕ) : Jan (Formula.uniqueSize n)
  | manyLarge (n : ℕ) : Jan (Formula.manyLarge n)

/-- The extension of Janiczak's axioms by the positive and negative class-size sentences. -/
inductive Signed (P N : Set ℕ) : Set Formula
  | jan {p} : Jan p → Signed P N p
  | pos {i} : i ∈ P → Signed P N (sizeSentence i)
  | neg {i} : i ∈ N → Signed P N (Formula.neg (sizeSentence i))

end Janiczak
