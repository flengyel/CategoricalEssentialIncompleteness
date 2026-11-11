/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46StableListComparison

/-! # Checks for the free-syntax interpretation prerequisites -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}

open StableListAlgebra.Comparison
variable (L M N : StableListAlgebra V)

example : map L M ≫ map M N = map L N := comp L M N
example : L.algebra.carrier ≅ M.algebra.carrier := iso L M
example : L.singleton ≫ map L M = M.singleton := singleton L M
example : L.append ≫ map L M = prod.map (map L M) (map L M) ≫ M.append := append L M
example (E : DecidableVariables V) : L.deletion E ≫ map L M =
    prod.map (𝟙 V) (map L M) ≫ M.deletion E := deletion L M E

example (E : DecidableVariables V) : prod.map (𝟙 V) (map L M) ≫ M.membership E =
    L.membership E := membership L M E

#print axioms CategoricalEssentialIncompleteness.V46.StableListAlgebra.Comparison.iso
#print axioms CategoricalEssentialIncompleteness.V46.StableListAlgebra.Comparison.append
#print axioms CategoricalEssentialIncompleteness.V46.StableListAlgebra.Comparison.deletion

#print axioms CategoricalEssentialIncompleteness.V46.StableListAlgebra.Comparison.membership
