/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCoverSemantics


/-! # Statement checks in `V46MillerCoverSemanticsChecks` -/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
example (p : ℕ → Fin 2) (e n m : ℕ) :
    (∃ r, Certified (bitPrefix p r) (e,n) m) ↔
      ∀ q : ℕ → Fin 2, rho q = rho p → m ∈ OracleProgram.numberedEval e q n :=
  search_correct p (e,n) m
example (u : List (Fin 2)) (e n m : ℕ) (h : Certified u (e,n) m)
    (p : ℕ → Fin 2) (hp : bitPrefix p u.length = u) (q : ℕ → Fin 2)
    (hq : rho q = rho p) : m ∈ OracleProgram.numberedEval e q n :=
  certified_sound u (e,n) m h p hp q hq
example (u : List (Fin 2)) (e n m m' : ℕ) :
    Certified u (e,n) m → Certified u (e,n) m' → m = m' := certified_unique u (e,n) m m'
example (p : ℕ → Fin 2) (e n m : ℕ)
    (h : ∀ q : ℕ → Fin 2, rho q = rho p → m ∈ OracleProgram.numberedEval e q n) :
    ∃ L : List (List (Fin 2)), FiniteCover.covers L = true ∧
      ∀ s ∈ L, ∃ r, Good (bitPrefix p r) (e,n) m s := finite_good_cover p (e,n) m h
end CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
