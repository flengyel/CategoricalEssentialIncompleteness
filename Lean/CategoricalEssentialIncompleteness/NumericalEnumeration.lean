/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalCategory
public import Mathlib.Data.Nat.Nth

/-!
# Computable enumeration of numerical objects

The increasing enumeration of an infinite recursive subset of `ℕ` is computable.
Counting its elements below a given bound supplies a computable inverse on the
subset. These functions will give an isomorphism between each numerical object
and the distinguished object of all natural numbers.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace CategoricalEssentialIncompleteness

/-- Counting the elements of a recursive predicate below a bound is computable. -/
theorem computable_count (p : ℕ → Prop) [DecidablePred p]
    (hp : ComputablePred p) : Computable (Nat.count p) := by
  have hind : Computable fun a : ℕ × (ℕ × ℕ) => if p a.2.1 then 1 else 0 :=
    (Computable.cond (hp.decide.comp (Computable.fst.comp Computable.snd))
      (Computable.const 1) (Computable.const 0)).of_eq fun a => by simp
  have hstep : Computable₂ fun _ : ℕ => fun q : ℕ × ℕ =>
      q.2 + if p q.1 then 1 else 0 :=
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd) hind).to₂
  refine (Computable.nat_rec Computable.id (Computable.const 0) hstep).of_eq ?_
  intro n
  induction n with
  | zero => exact (Nat.count_zero p).symm
  | succ n ih =>
    simp only [id_eq] at ih ⊢
    rw [ih, Nat.count_succ]

/-- The increasing enumeration of an infinite recursive predicate is computable. -/
theorem computable_nth (p : ℕ → Prop) (hp : ComputablePred p)
    (hinf : (Set.ofPred p).Infinite) : Computable (Nat.nth p) := by
  classical
  have hcount := computable_count p hp
  have htest : Computable₂ fun n k : ℕ => decide (p k ∧ Nat.count p k = n) := by
    exact (Primrec.and.to_comp.comp (hp.decide.comp Computable.snd)
      (Primrec.eq.decide.to_comp.comp (hcount.comp Computable.snd)
        Computable.fst)).of_eq fun _ => by simp
  have hsearch : Partrec fun n : ℕ =>
      Nat.rfind (fun k => Part.some (decide (p k ∧ Nat.count p k = n))) :=
    Partrec.rfind htest.partrec₂
  refine hsearch.of_eq_tot fun n => ?_
  have hdom : (Nat.rfind (fun k =>
      Part.some (decide (p k ∧ Nat.count p k = n)))).Dom := by
    apply Nat.rfind_dom.mpr
    refine ⟨Nat.nth p n, ?_, fun _ => trivial⟩
    simp [Nat.nth_mem_of_infinite hinf, Nat.count_nth_of_infinite hinf]
  have hmem := Part.get_mem hdom
  have hspec := of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hmem)).symm
  have heq := Nat.nth_count hspec.1
  rw [hspec.2] at heq
  exact heq.symm ▸ hmem

namespace Numerical

/-- The increasing enumeration of a numerical object. -/
def enumerate (X : Numerical) : ℕ → ℕ := Nat.nth (· ∈ X.carrier)

/-- The number of elements of a numerical object below the given natural number. -/
def rank (X : Numerical) : ℕ → ℕ := by
  classical
  exact Nat.count (· ∈ X.carrier)

theorem enumerate_computable (X : Numerical) : Computable (enumerate X) :=
  computable_nth _ X.recursive X.infinite

theorem rank_computable (X : Numerical) : Computable (rank X) := by
  classical
  exact computable_count _ X.recursive

theorem enumerate_mem (X : Numerical) (n : ℕ) : enumerate X n ∈ X.carrier :=
  Nat.nth_mem_of_infinite X.infinite n

theorem enumerate_injective (X : Numerical) : Function.Injective (enumerate X) :=
  Nat.nth_injective X.infinite

@[simp] theorem rank_enumerate (X : Numerical) (n : ℕ) :
    rank X (enumerate X n) = n := by
  classical
  exact Nat.count_nth_of_infinite (p := fun k => k ∈ X.carrier) X.infinite n

theorem enumerate_rank (X : Numerical) {n : ℕ} (hn : n ∈ X.carrier) :
    enumerate X (rank X n) = n := by
  classical
  exact Nat.nth_count hn

theorem enumerate_surjective (X : Numerical) {n : ℕ} (hn : n ∈ X.carrier) :
    ∃ k, enumerate X k = n :=
  ⟨rank X n, enumerate_rank X hn⟩

end Numerical
end CategoricalEssentialIncompleteness
