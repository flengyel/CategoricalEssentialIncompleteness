/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutInseparabilityRelative


/-! # Decision predicates relative to a single representation -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.Checks

example (p : Bits) (h : ℕ → ℕ) (hh : Computable h) :
    Complementary (fixedGuard p h hh 1) (fixedGuard p h hh 0) :=
  fixedGuard_complementary p h hh

example (z : Point) (p : Bits) (hp : p ∈ representations z) :
    Uniform.support (pair0 ((Uniform.J z p hp).toFunctor.map (Uniform.tau z))) =
      Uniform.support (diagonal0 z) := mapped_pair0_support z p hp

example (z : Point) (h : ℕ → ℕ) (hh : Computable h)
    (h₀ : h ⁻¹' {n | (z n : ℝ) < 1/2} = Uniform.support (diagonal0 z))
    (h₁ : h ⁻¹' {n | 1/2 < (z n : ℝ)} = Uniform.support (diagonal1 z))
    (p : Bits) (hp : p ∈ representations z) :
    ¬RecursionCategory.IsTuringMorphism ((Uniform.J z p hp).toFunctor.map (Uniform.tau z)) :=
  mapped_tau_notTuring_of_recursive_reduction z h hh h₀ h₁ p hp

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.Checks
