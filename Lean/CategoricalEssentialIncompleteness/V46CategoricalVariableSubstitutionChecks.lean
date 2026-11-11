/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalVariableSubstitution

/-! # Checks for the free-syntax interpretation prerequisites -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}


variable {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
example : (constantFamilyFunctor S.substitutionParameters).map S.variableConstructor ≫
    S.substitutionFold.1 = parameterHom S.variableSubstitutionPair := S.variable_fold_in_slice
example {Z : D} (p : Z ⟶ S.substitutionParameters) (y : Z ⟶ V) :
    prod.lift (y ≫ S.variableConstructor) p ≫ S.termSubstitution =
      Two.branch (prod.lift y (p ≫ prod.fst) ≫ S.decidableVariables.test)
        (y ≫ S.variableConstructor) (p ≫ prod.snd) := S.variable_substitution p y

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.variable_fold_in_slice
#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.variable_substitution
