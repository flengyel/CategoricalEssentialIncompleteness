/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportFamilies


/-! # Statement checks in `V46SyntaxSubstitutionTransportFamiliesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open CategoricalEssentialIncompleteness.V46.SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
example (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
    {X Y : C} {X' Y' : D} (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (h : P ⨯ X ⟶ Y) (h' : Q ⨯ X' ⟶ Y')
    (hh : E.functor.map h ≫ j.hom = (SyntaxOptionTransport.productIso E b i).hom ≫ h') :
    (sliceEquivalence E b).functor.map (parameterHom h) ≫
        (coefficientComparison E b Y Y' j).hom =
      (coefficientComparison E b X X' i).hom ≫ parameterHom h' :=
  map_substitution_parameterHom E b i j h h' hh
