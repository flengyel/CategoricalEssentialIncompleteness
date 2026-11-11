/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsStable


/-! # Statement checks in `V46MillerListsStableChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (R : Total.TotalCategory P) (V : Total.Carrier P)
example : StableListAlgebra (⟨V⟩ : Total.TotalCategory P) := Lists.stable V
example : (Lists.stable V).algebra.carrier=Lists.object V := rfl
example : IsInitial ((Lists.stable V).algebra.withParameters R).asAlgebra := (Lists.stable V).stable R
example : (Lists.parameterAlgebra R V).nil ≫ (Syntax.Raw.explicitFamilyIso R (Lists.object V)).hom=
    ((Lists.algebra V).withParameters R).nil := Lists.parameterAlgebra_nil R V
example : (Lists.parameterAlgebra R V).cons ≫ (Syntax.Raw.explicitFamilyIso R (Lists.object V)).hom=
    prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P)))
      (Syntax.Raw.explicitFamilyIso R (Lists.object V)).hom ≫ ((Lists.algebra V).withParameters R).cons :=
  Lists.parameterAlgebra_cons R V
