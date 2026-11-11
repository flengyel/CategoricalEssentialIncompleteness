/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkFormulaCoding
public import Mathlib.Data.Finset.Union

/-! # The manuscript's finite Hilbert proof trees -/

@[expose] public section

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open Formula

def H1 (p q : Formula) : Formula := .imp p (.imp q p)
def H2 (p q r : Formula) : Formula :=
  .imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r))
def H3 (p q : Formula) : Formula := .imp (.imp (.neg q) (.neg p)) (.imp p q)

inductive ProofTree where
  | logical1 : Formula → Formula → ProofTree
  | logical2 : Formula → Formula → Formula → ProofTree
  | logical3 : Formula → Formula → ProofTree
  | positive : ℕ → ProofTree
  | negative : ℕ → ProofTree
  | mp : ProofTree → ProofTree → ProofTree

inductive Concludes (A B : Set ℕ) : ProofTree → Formula → Prop
  | logical1 (p q) : Concludes A B (.logical1 p q) (H1 p q)
  | logical2 (p q r) : Concludes A B (.logical2 p q r) (H2 p q r)
  | logical3 (p q) : Concludes A B (.logical3 p q) (H3 p q)
  | positive {x} : x ∈ A → Concludes A B (.positive x) (.atom x)
  | negative {x} : x ∈ B → Concludes A B (.negative x) (.neg (.atom x))
  | mp {t u p q} : Concludes A B t p → Concludes A B u (.imp p q) →
      Concludes A B (.mp t u) q

def ProofTree.positiveLabels : ProofTree → Finset ℕ
  | .positive x => {x}
  | .mp t u => t.positiveLabels ∪ u.positiveLabels
  | _ => ∅

def ProofTree.negativeLabels : ProofTree → Finset ℕ
  | .negative x => {x}
  | .mp t u => t.negativeLabels ∪ u.negativeLabels
  | _ => ∅

theorem Concludes.positive_supported {A B : Set ℕ} {t : ProofTree} {p : Formula}
    (h : Concludes A B t p) : ∀ x ∈ t.positiveLabels,x ∈ A := by
  induction h with
  | logical1 | logical2 | logical3 | negative => simp [ProofTree.positiveLabels]
  | @positive x hx => simpa [ProofTree.positiveLabels] using hx
  | mp _ _ ih1 ih2 =>
    intro x hx
    exact (Finset.mem_union.mp hx).elim (ih1 x) (ih2 x)

theorem Concludes.negative_supported {A B : Set ℕ} {t : ProofTree} {p : Formula}
    (h : Concludes A B t p) : ∀ x ∈ t.negativeLabels,x ∈ B := by
  induction h with
  | logical1 | logical2 | logical3 | positive => simp [ProofTree.negativeLabels]
  | @negative x hx => simpa [ProofTree.negativeLabels] using hx
  | mp _ _ ih1 ih2 =>
    intro x hx
    exact (Finset.mem_union.mp hx).elim (ih1 x) (ih2 x)

theorem Concludes.sound {A B : Set ℕ} {t : ProofTree} {p : Formula}
    (h : Concludes A B t p) (v : ℕ → Prop)
    (hp : ∀ x ∈ t.positiveLabels,v x) (hn : ∀ x ∈ t.negativeLabels,¬ v x) : eval v p := by
  classical
  induction h with
  | logical1 => exact fun h _ => h
  | logical2 => simp only [H2,eval]; tauto
  | logical3 => simp only [H3,eval]; tauto
  | @positive x _ => exact hp x (Finset.mem_singleton_self x)
  | @negative x _ => exact hn x (Finset.mem_singleton_self x)
  | mp _ _ ih1 ih2 =>
    exact (ih2 (fun x hx => hp x (Finset.mem_union.mpr (Or.inr hx)))
      (fun x hx => hn x (Finset.mem_union.mpr (Or.inr hx))))
      (ih1 (fun x hx => hp x (Finset.mem_union.mpr (Or.inl hx)))
        (fun x hx => hn x (Finset.mem_union.mpr (Or.inl hx))))

def Theorems (A B : Set ℕ) : Set Formula := {p | ∃ t,Concludes A B t p}

theorem finite_valuation_consistency {A B : Set ℕ} (hd : Disjoint A B)
    (p : Formula) : ¬ (p ∈ Theorems A B ∧ .neg p ∈ Theorems A B) := by
  rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
  let L := t.positiveLabels ∪ u.positiveLabels
  let v : ℕ → Prop := fun x => x ∈ L
  have hL : ∀ x ∈ L,x ∈ A := by
    intro x hx
    exact (Finset.mem_union.mp hx).elim (ht.positive_supported x) (hu.positive_supported x)
  have htn : ∀ x ∈ t.negativeLabels,¬ v x := by
    intro x hx hxl
    exact Set.disjoint_left.mp hd (hL x hxl) (ht.negative_supported x hx)
  have hun : ∀ x ∈ u.negativeLabels,¬ v x := by
    intro x hx hxl
    exact Set.disjoint_left.mp hd (hL x hxl) (hu.negative_supported x hx)
  exact hu.sound v (fun x hx => Finset.mem_union.mpr (Or.inr hx)) hun
    (ht.sound v (fun x hx => Finset.mem_union.mpr (Or.inl hx)) htn)

theorem theorem_least {A B : Set ℕ} {T : Set Formula}
    (h1 : ∀ p q,H1 p q ∈ T) (h2 : ∀ p q r,H2 p q r ∈ T) (h3 : ∀ p q,H3 p q ∈ T)
    (ha : ∀ x ∈ A,.atom x ∈ T) (hb : ∀ x ∈ B,.neg (.atom x) ∈ T)
    (hm : ∀ p q,p ∈ T → .imp p q ∈ T → q ∈ T) : Theorems A B ⊆ T := by
  rintro p ⟨t,ht⟩
  induction ht with
  | logical1 p q => exact h1 p q
  | logical2 p q r => exact h2 p q r
  | logical3 p q => exact h3 p q
  | positive hx => exact ha _ hx
  | negative hx => exact hb _ hx
  | mp _ _ ih1 ih2 => exact hm _ _ ih1 ih2

def ProofTree.mapAtoms (f : ℕ → ℕ) : ProofTree → ProofTree
  | .logical1 p q => .logical1 (Formula.mapAtoms f p) (Formula.mapAtoms f q)
  | .logical2 p q r => .logical2 (Formula.mapAtoms f p) (Formula.mapAtoms f q) (Formula.mapAtoms f r)
  | .logical3 p q => .logical3 (Formula.mapAtoms f p) (Formula.mapAtoms f q)
  | .positive x => .positive (f x)
  | .negative x => .negative (f x)
  | .mp t u => .mp (t.mapAtoms f) (u.mapAtoms f)

theorem Concludes.mapAtoms {A B A' B' : Set ℕ} {t : ProofTree} {p : Formula}
    (h : Concludes A B t p) (f : ℕ → ℕ)
    (ha : ∀ x ∈ A,f x ∈ A') (hb : ∀ x ∈ B,f x ∈ B') :
    Concludes A' B' (t.mapAtoms f) (p.mapAtoms f) := by
  induction h with
  | logical1 => exact Concludes.logical1 _ _
  | logical2 => exact Concludes.logical2 _ _ _
  | logical3 => exact Concludes.logical3 _ _
  | positive hx => exact Concludes.positive (ha _ hx)
  | negative hx => exact Concludes.negative (hb _ hx)
  | mp _ _ ih1 ih2 => exact Concludes.mp ih1 ih2

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
