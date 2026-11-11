/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxBooleanTransport


/-! # Statement checks in `V46SyntaxBooleanTransportChecks` -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxBooleanTransportChecks
open SyntaxOperationsTransport DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)
example (X : C) (b : Bool) :
    E.functor.map (Two.constant X b) ≫ (booleanIso E).hom =
      Two.constant (E.functor.obj X) b := map_constant E X b
example {X Y : C} (χ : X ⟶ Two C) (f g : X ⟶ Y) :
    E.functor.map (Two.branch χ f g) =
      Two.branch (E.functor.map χ ≫ (booleanIso E).hom)
        (E.functor.map f) (E.functor.map g) := map_branch E χ f g
example {V : C} (a b : DecidableVariables V) : a.test = b.test := equality_test_unique a b
end CategoricalEssentialIncompleteness.V46.SyntaxBooleanTransportChecks
