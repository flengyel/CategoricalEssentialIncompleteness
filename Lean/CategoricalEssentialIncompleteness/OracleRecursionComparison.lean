/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleApproximationSearch

/-! # Every oracle recursive function admits ordinary finite-query approximations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

def oracleFunction (S : Set ℕ) : ℕ → Part ℕ := fun n => Part.some (answer S n)
def oracleSet (S : Set ℕ) : Set (ℕ → Part ℕ) := {oracleFunction S}

theorem recursiveIn_hasApproximation {S : Set ℕ} {f : ℕ → Part ℕ}
    (hf : Nat.RecursiveIn (oracleSet S) f) : HasApproximation S f := by
  induction hf with
  | zero => exact HasApproximation.of_partrec (Partrec.nat_iff.mpr Nat.Partrec.zero)
  | succ => exact HasApproximation.of_partrec (Partrec.nat_iff.mpr Nat.Partrec.succ)
  | left => exact HasApproximation.of_partrec (Partrec.nat_iff.mpr Nat.Partrec.left)
  | right => exact HasApproximation.of_partrec (Partrec.nat_iff.mpr Nat.Partrec.right)
  | oracle g hg =>
    have he : g=oracleFunction S := Set.mem_singleton_iff.mp hg
    subst g
    exact HasApproximation.oracle
  | pair hf hg ihf ihg =>
    refine (ihf.pair ihg).of_eq ?_
    intro n
    simp [Seq.seq,Part.bind_map]
  | comp hf hg ihf ihg => exact ihf.comp ihg
  | @prec f g hf hg ihf ihg =>
    refine (ihf.prec ihg).of_eq ?_
    intro p
    rcases Nat.unpair p with ⟨a,n⟩
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [iteration,Part.bind_eq_bind] using
        congrArg (fun k : Part ℕ => k.bind (fun i => g (Nat.pair a (Nat.pair n i)))) ih
  | rfind hf ih => exact ih.rfind

theorem HasApproximation.domain {S : Set ℕ} {f : ℕ → Part ℕ}
    (hf : HasApproximation S f) : FiniteOracleRE S (fun x => (f x).Dom) := by
  obtain ⟨F,hF,hM,hf⟩ := hf
  have hr : REPred (fun p : ℕ × List ℕ => (F (p.2,p.1)).Dom) :=
    (hF.comp (Computable.pair Computable.snd Computable.fst)).dom_re
  refine ⟨fun p => (F (p.2,p.1)).Dom,hr,?_,?_⟩
  · intro x l l' hl h
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
    exact Part.dom_iff_mem.mpr ⟨y,hM l l' hl x y hy⟩
  · intro x
    constructor
    · intro h
      obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp h
      obtain ⟨n,hn⟩ := (hf x y).mp hy
      exact ⟨n,Part.dom_iff_mem.mpr ⟨y,hn⟩⟩
    · rintro ⟨n,hn⟩
      obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp hn
      exact Part.dom_iff_mem.mpr ⟨y,(hf x y).mpr ⟨n,hy⟩⟩

/-- Oracle recursion is interpreted over the full characteristic oracle,
including negative answers, and every one of its domains is represented. -/
theorem recursiveIn_domain {S : Set ℕ} {f : ℕ → Part ℕ}
    (hf : Nat.RecursiveIn (oracleSet S) f) : FiniteOracleRE S (fun x => (f x).Dom) :=
  (recursiveIn_hasApproximation hf).domain

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
