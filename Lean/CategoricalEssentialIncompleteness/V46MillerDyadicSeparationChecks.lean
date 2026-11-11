/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDyadicSeparation


/-! # Statement checks in `V46MillerDyadicSeparationChecks` -/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Checks
example (b c : ℕ → Fin 2) : Real.ofDigits b < Real.ofDigits c ↔
    ∃ k, numeral b k+1 < numeral c k :=
  ⟨exists_numeral_separation b c,fun ⟨k,h⟩ => numeral_separation b c k h⟩
example (u s : List (Fin 2)) (n k : ℕ) (h : ApartAt u s n k)
    (p q : ℕ → Fin 2) (hp : bitPrefix p u.length = u) (hq : bitPrefix q s.length = s) :
    rho p ≠ rho q := apartAt_sound u s n k h p q hp hq
example (p q : ℕ → Fin 2) (h : rho p ≠ rho q) :
    ∃ n k, ApartAt (bitPrefix p (queryBound n k))
      (bitPrefix q (queryBound n k)) n k := exists_apartAt p q h
example (u v s : List (Fin 2)) (n k : ℕ) (h : u <+: v) :
    ApartAt u s n k → ApartAt v s n k := apartAt_mono_left u v s n k h
example (b : ℕ → Fin 2) (k : ℕ) :
    (numeral b k : ℝ)/(2 : ℝ)^k ≤ Real.ofDigits b ∧
      Real.ofDigits b ≤ ((numeral b k : ℝ)+1)/(2 : ℝ)^k := numeral_bounds b k
end CategoricalEssentialIncompleteness.V46.Miller.Checks
