/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# From a parameterized diagonal calculation to an equalizer factorization

For an enriched application, the category and predicate lattices in `D` must
be those of arrows parameterized by `T`. A representation at that parameter,
together with interpretation of the two lattice bounds, gives a morphism to
their equalizer. A calculation restricted to global elements does not supply
these parameterized data.
-/

set_option autoImplicit false

noncomputable section

universe v u w w' v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness

variable {A : Type u} [Category.{v} A] [HasBinaryProducts A]
variable {E : PredicateLattice.{v, u, w} A} {P : PredicateLattice.{v, u, w'} A}
variable {V : Type u'} [Category.{v'} V] [HasFiniteLimits V]

/-- Interpretation of the domain lattice at a parameter object, including its bounds. -/
structure BoundInterpretation (D : DiagonalData E P) (T EU : V)
    (zero one : ⊤_ V ⟶ EU) where
  realize : E.obj D.U → (T ⟶ EU)
  realize_bot : realize ⊥ = terminal.from T ≫ zero
  realize_top : realize ⊤ = terminal.from T ≫ one

/-- The finite-limit bridge for `thm:internal-inseparability`.
Here `T` may be the separator object. The separator and its representative
belong to the parameterized data, rather than to the global-point data. -/
theorem parameterized_separator_factorization (D : DiagonalData E P)
    {T EU : V} {zero one : ⊤_ V ⟶ EU}
    (interpret : BoundInterpretation D T EU zero one)
    (a : ComplementaryPair (E.obj D.S)) (ha : D.Separates a)
    (g : D.U ⟶ D.U) (hg : D.Represents (D.diagonalPair a) g) :
    ∃ factor : T ⟶ equalizer zero one,
      factor ≫ equalizer.ι zero one = terminal.from T := by
  have h := congrArg interpret.realize (D.diagonal_collapse a ha g hg)
  rw [interpret.realize_bot, interpret.realize_top] at h
  exact ⟨equalizer.lift (terminal.from T) h, equalizer.lift_ι _ _⟩

/-- A global point of the factorizing object equates the original global bounds. -/
theorem no_global_point_of_factorization {T EU : V} {zero one : ⊤_ V ⟶ EU}
    (hne : zero ≠ one) (factor : T ⟶ equalizer zero one) :
    IsEmpty (⊤_ V ⟶ T) := by
  constructor
  intro point
  apply hne
  have h := congrArg (fun k => (point ≫ factor) ≫ k) (equalizer.condition zero one)
  simpa only [← Category.assoc, terminal.hom_ext ((point ≫ factor) ≫
    equalizer.ι zero one) (𝟙 _), Category.id_comp] using h

end CategoricalEssentialIncompleteness
