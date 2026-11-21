/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationEquality


/-! # Internal numerical equality on every uniform carrier -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family}
example (X : Total.TotalCategory P) : DecidableVariables X := Derivation.equality X
example (X : Total.TotalCategory P) :
    IsPullback (prod.lift (𝟙 X) (𝟙 X)) (terminal.from X) (Derivation.equality X).test coprod.inr :=
  (Derivation.equality X).diagonal
example {X W : Total.TotalCategory P} (f g : W ⟶ X) :
    prod.lift f g ≫ (Derivation.equality X).test=Two.constant W true ↔ f=g :=
  (Derivation.equality X).test_true_iff f g
