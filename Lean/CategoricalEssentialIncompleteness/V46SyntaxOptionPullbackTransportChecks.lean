/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOptionPullbackTransport


/-! # Statement checks in `V46SyntaxOptionPullbackTransportChecks` -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOptionTransportChecks
open SyntaxOptionTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)
local notation "F" => E.functor
example {W Y : C} {W' Y' : D}
    (i : E.functor.obj W ≅ W') (j : E.functor.obj Y ≅ Y')
    (f : W ⟶ OptionSyntax.obj Y) (f' : W' ⟶ OptionSyntax.obj Y')
    (hf : E.functor.map f ≫ (optionIso E j).hom = i.hom ≫ f') :
    (successIso E i j f f' hf).hom ≫ pullback.fst f' coprod.inr =
      E.functor.map (pullback.fst f coprod.inr) ≫ i.hom := successIso_fst E i j f f' hf
example {W Y : C} {W' Y' : D}
    (i : E.functor.obj W ≅ W') (j : E.functor.obj Y ≅ Y')
    (f : W ⟶ OptionSyntax.obj Y) (f' : W' ⟶ OptionSyntax.obj Y')
    (hf : E.functor.map f ≫ (optionIso E j).hom = i.hom ≫ f') :
    (successIso E i j f f' hf).hom ≫ pullback.snd f' coprod.inr =
      E.functor.map (pullback.snd f coprod.inr) ≫ j.hom := successIso_snd E i j f f' hf
end CategoricalEssentialIncompleteness.V46.SyntaxOptionTransportChecks
