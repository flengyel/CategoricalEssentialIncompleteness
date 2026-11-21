/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportMembership


/-! # Membership is transported by its parameter algebra and its proved Boolean constructor diagrams, rather than by an assumed fold law -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open CategoricalEssentialIncompleteness.V46.SyntacticLists.Transport
open CategoricalEssentialIncompleteness.V46.DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]

example (E : C ≌ D) (V : C) (W : D) (e : E.functor.obj V ≅ W)
    (S : DecidableVariables V) (T : DecidableVariables W) (L : StableListAlgebra V) :
    E.functor.map (L.membership S) ≫ (booleanIso E).hom =
      prodComparison E.functor V L.algebra.carrier ≫ prod.map e.hom (𝟙 _) ≫
        (mappedStableListAlgebra E V W e L).membership T :=
  map_list_membership E V W e S T L
