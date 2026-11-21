/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOptionTransport


/-! # Option and product comparisons through an equivalence -/

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
example {W X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    E.functor.map (OptionSyntax.fail : W ⟶ OptionSyntax.obj X) ≫ (optionIso E i).hom =
      (OptionSyntax.fail : E.functor.obj W ⟶ OptionSyntax.obj X') := map_fail E i
example {X Y : C} {X' Y' : D} (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (hf : E.functor.map f ≫ j.hom = i.hom ≫ g) :
    E.functor.map (OptionSyntax.map f) ≫ (optionIso E j).hom =
      (optionIso E i).hom ≫ OptionSyntax.map g := map_option_map E i j f g hf
end CategoricalEssentialIncompleteness.V46.SyntaxOptionTransportChecks
