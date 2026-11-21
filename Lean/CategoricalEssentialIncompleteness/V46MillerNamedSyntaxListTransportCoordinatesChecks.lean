/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportCoordinates


/-! # Coordinates of lists of variable names -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedSyntaxComparison.ListTransport
variable {C D : Type} [Category C] [Category D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
example (U X Y : C) (X' Y' : D) (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') :
    (listStepComparison F U X Y X' Y' i j).hom.left ≫ listStepHead (F.obj U) X' Y'=
      F.map (listStepHead U X Y) ≫ i.hom := listStepComparison_head F U X Y X' Y' i j
example (U X Y : C) (X' Y' : D) (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') :
    (listStepComparison F U X Y X' Y' i j).hom.left ≫ listStepValue (F.obj U) X' Y'=
      F.map (listStepValue U X Y) ≫ j.hom := listStepComparison_value F U X Y X' Y' i j
example {V Y : C} {Y' : D} (j : F.obj Y ≅ Y') (S : DecidableVariables V) :
    (listStepComparison F V V Y (F.obj V) Y' (Iso.refl _) j).hom.left ≫
      (prod.lift (constantFamily (F.obj V) (F.obj V) ⨯ constantFamily (F.obj V) Y').hom
        (listStepHead (F.obj V) (F.obj V) Y') ≫ (Derivation.mappedEquality F S).test)=
      F.map (prod.lift (constantFamily V V ⨯ constantFamily V Y).hom (listStepHead V V Y) ≫ S.test) ≫
        (Derivation.booleanIso F).hom := listStepComparison_test F j S
