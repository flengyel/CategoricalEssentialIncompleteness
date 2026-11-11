/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46VariableTests

/-! # Checks for the free-syntax interpretation prerequisites -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}

example (E F : DecidableVariables V) : E.test = F.test := E.test_unique F
example (E F : DecidableVariables V) : E = F := E.unique F

#print axioms CategoricalEssentialIncompleteness.V46.DecidableVariables.test_positive
#print axioms CategoricalEssentialIncompleteness.V46.DecidableVariables.test_unique

#print axioms CategoricalEssentialIncompleteness.V46.DecidableVariables.unique
