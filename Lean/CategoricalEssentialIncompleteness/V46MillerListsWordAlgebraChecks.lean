/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsWordAlgebra


/-! # Full constructor comparison between numerical lists and literal words -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (V : Total.Carrier P)
example : (Lists.algebra V).asAlgebra ≅ (Lists.literalAlgebra V).asAlgebra := Lists.wordAlgebraIso V
example : (Lists.wordAlgebraIso V).hom.f=(Lists.wordIso V).hom := rfl
example : (Lists.wordAlgebraIso V).inv.f=(Lists.wordIso V).inv := rfl
example : IsInitial (Lists.literalAlgebra V).asAlgebra := Lists.literalInitial V
example : (Lists.algebra V).nil ≫ (Lists.wordIso V).hom=(Lists.literalAlgebra V).nil :=
  Lists.wordMap_nil_constructor V
example : (Lists.algebra V).cons ≫ (Lists.wordIso V).hom=
    prod.map (𝟙 (⟨V⟩ : Total.TotalCategory P)) (Lists.wordIso V).hom ≫ (Lists.literalAlgebra V).cons :=
  Lists.wordMap_cons_constructor V
