/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOptionConstructorTransport


/-! # Statement checks in `V46SyntaxOptionConstructorTransportChecks` -/

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
example {V Y Z : C} {V' Y' Z' : D}
    (i : E.functor.obj V ≅ V') (j : E.functor.obj Y ≅ Y') (l : E.functor.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (hh : E.functor.map h ≫ l.hom = (productIso E i j).hom ≫ h') :
    E.functor.map (OptionSyntax.coefficient h) ≫ (optionIso E l).hom =
      (productIso E i (optionIso E j)).hom ≫ OptionSyntax.coefficient h' :=
  map_coefficient E i j l h h' hh
example {Y Z : C} {Y' Z' : D}
    (i : E.functor.obj Y ≅ Y') (j : E.functor.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (hh : E.functor.map h ≫ j.hom = (productIso E i i).hom ≫ h') :
    E.functor.map (OptionSyntax.binary h) ≫ (optionIso E j).hom =
      (productIso E (optionIso E i) (optionIso E i)).hom ≫ OptionSyntax.binary h' :=
  map_binary E i j h h' hh
end CategoricalEssentialIncompleteness.V46.SyntaxOptionTransportChecks
