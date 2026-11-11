/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportBooleans


/-! # Statement checks in `V46MillerNamedSyntaxListTransportBooleansChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedSyntaxComparison.ListTransport
variable {C D : Type} [Category C] [Category D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
example (X : C) (b : Bool) : F.map (Two.constant X b) ≫ (Derivation.booleanIso F).hom=
    Two.constant (F.obj X) b := map_constant F X b
example {X Y : C} (χ : X ⟶ Two C) (f g : X ⟶ Y) :
    F.map (Two.branch χ f g)=Two.branch (F.map χ ≫ (Derivation.booleanIso F).hom) (F.map f) (F.map g) :=
  map_branch F χ f g
example {X : C} (op : Bool → Bool → Bool) (f g : X ⟶ Two C) :
    F.map (Two.binary op f g) ≫ (Derivation.booleanIso F).hom=
      Two.binary op (F.map f ≫ (Derivation.booleanIso F).hom) (F.map g ≫ (Derivation.booleanIso F).hom) :=
  map_boolean_binary F op f g
example {V : C} (S : DecidableVariables V) :
    F.map S.test ≫ (Derivation.booleanIso F).hom=prodComparison F V V ≫ (Derivation.mappedEquality F S).test :=
  map_decidable_test F S
