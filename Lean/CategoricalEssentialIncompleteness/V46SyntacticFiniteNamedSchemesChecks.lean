/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticFiniteNamedSchemes


/-! # The seven parameter injections of a syntax algebra -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedSchemes.Checks
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {V : C} {σ π : ℕ → C} {d : ℕ} (S : CategoricalSyntax V σ π d)

example (i : Fin 7) : schemeInjection S i ≫ S.logicalAxioms = schemeMorphism S i :=
  schemeInjection_formula S i

example : schemeParameters S 3 = S.instantiationParameters := rfl
example : schemeParameters S 6 = S.equalitySchemeParameters := rfl
end CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedSchemes.Checks
