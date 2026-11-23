/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakCoding
public import Foundation.Vorspiel.Computability

/-! # Enumeration of the signed finite-class axioms -/

@[expose] public section

set_option autoImplicit false

namespace Janiczak
open Formula

namespace Formula.Effective
variable {α : Type} [Primcodable α]

theorem atLeast {n r : α → ℕ} (hn : Primrec n) (hr : Primrec r) :
    Effective (fun x => Formula.atLeast (n x) (r x)) :=
  exBlock (Primrec.const 0) hn ((distinctBelow hn).conj
    (conjBelow (related (hr.comp Primrec.fst) Primrec.snd) hn))

theorem uniqueSize : Effective Formula.uniqueSize := by
  have u := Primrec.succ
  have v := Primrec.succ.comp Primrec.succ
  exact all u (all v (imp ((exactly Primrec.id u).conj (exactly Primrec.id v)) (related u v)))

theorem manyLarge : Effective Formula.manyLarge := by
  open Primrec in
  have p : Primrec (fun t : ℕ × ℕ => t.1+1+t.2) := nat_add.comp (succ.comp fst) snd
  open Primrec in
  have r : Effective (fun t : (ℕ × ℕ) × ℕ => (Formula.related (t.1.1+1+t.2) (t.1.1+1+t.1.2)).neg) :=
    (related (nat_add.comp ((succ.comp fst).comp fst) snd) (p.comp fst)).neg
  open Primrec in
  exact exBlock succ Primrec.id
    ((conjBelow (f := fun n j => Formula.conjBelow
        (fun i => (Formula.related (n+1+i) (n+1+j)).neg) j)
        (conjBelow (f := fun t : ℕ × ℕ => fun i => (Formula.related (t.1+1+i) (t.1+1+t.2)).neg) r snd)
        Primrec.id).conj
      (conjBelow (f := fun n i => Formula.atLeast n (n+1+i)) (atLeast fst p) Primrec.id))
end Formula.Effective

def codeSet (T : Set Formula) : Set ℕ := {w | ∃ p ∈ T, p.code = w}

theorem enumerable_image {P : Set ℕ} (hP : REPred (· ∈ P)) (f : ℕ → ℕ) (hf : Computable f) :
    REPred (fun w => ∃ i, i ∈ P ∧ f i = w) := by
  have eq' : REPred (fun x : ℕ × ℕ => f x.2 = x.1) :=
    (Primrec.eq (α := ℕ)).computablePred.to_re.comp ((hf.comp Computable.snd).pair Computable.fst)
  exact ((hP.comp Computable.snd).and eq').projection

/-- The finite relation laws and the two schematic families enumerate the base theory. -/
theorem jan_axioms_enumerable : REPred (· ∈ codeSet Jan) := by
  have point (a : ℕ) : REPred (fun w : ℕ => a = w) :=
    (Primrec.eq.comp (Primrec.const a) Primrec.id).computablePred.to_re
  have univ : REPred (fun n : ℕ => n ∈ (Set.univ : Set ℕ)) :=
    ((Primrec.eq.comp (Primrec.id (α := ℕ)) Primrec.id).computablePred.to_re).of_eq (by simp)
  have range (f : ℕ → ℕ) (hf : Computable f) : REPred (fun w => ∃ n, f n = w) :=
    (enumerable_image (P := Set.univ) univ f hf).of_eq
      (fun _ => by simp)
  apply (((((point reflSentence.code).or (point symmSentence.code)).or (point transSentence.code)).or
    (range _ Effective.uniqueSize.to_comp)).or (range _ Effective.manyLarge.to_comp)).of_eq
  intro w
  constructor
  · rintro ((((h | h) | h) | ⟨n,h⟩) | ⟨n,h⟩)
    · exact ⟨_,.refl,h⟩
    · exact ⟨_,.symm,h⟩
    · exact ⟨_,.trans,h⟩
    · exact ⟨_,.uniqueSize n,h⟩
    · exact ⟨_,.manyLarge n,h⟩
  · rintro ⟨p,h,rfl⟩
    cases h with
    | refl => exact Or.inl (Or.inl (Or.inl (Or.inl rfl)))
    | symm => exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
    | trans => exact Or.inl (Or.inl (Or.inr rfl))
    | uniqueSize n => exact Or.inl (Or.inr ⟨n,rfl⟩)
    | manyLarge n => exact Or.inr ⟨n,rfl⟩

theorem signed_axioms_enumerable {P N : Set ℕ} (hP : REPred (· ∈ P)) (hN : REPred (· ∈ N)) :
    REPred (· ∈ codeSet (Signed P N)) := by
  have neg : Effective (fun i => (sizeSentence i).neg) := Effective.neg primrec_sizeSentence
  apply ((jan_axioms_enumerable.or (enumerable_image hP _ primrec_sizeSentence.to_comp)).or
    (enumerable_image hN _ neg.to_comp)).of_eq
  intro w
  constructor
  · rintro ((⟨p,h,hw⟩ | ⟨i,hi,hw⟩) | ⟨i,hi,hw⟩)
    · exact ⟨p,.jan h,hw⟩
    · exact ⟨_,.pos hi,hw⟩
    · exact ⟨_,.neg hi,hw⟩
  · rintro ⟨p,h,rfl⟩
    cases h with
    | jan h => exact Or.inl (Or.inl ⟨_,h,rfl⟩)
    | pos hi => exact Or.inl (Or.inr ⟨_,hi,rfl⟩)
    | neg hi => exact Or.inr ⟨_,hi,rfl⟩

end Janiczak
