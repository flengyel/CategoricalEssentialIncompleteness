import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportCoordinates

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

example (E : C ≌ D) (V : C) (W : D) (e : E.functor.obj V ≅ W) (L : StableListAlgebra V) :
    E.functor.map L.singleton = e.hom ≫ (mappedStableListAlgebra E V W e L).singleton :=
  map_list_singleton E V W e L
