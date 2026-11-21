/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransport

/-!
Constructor comparisons for transported list algebras. This layer needs only finite
products and coproducts, so it also applies to the parameter-slice equivalences
without any RegularOver assumption.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable [HasFiniteProducts D] [HasFiniteCoproducts D]
variable (E : C ≌ D) (V : C) (W : D) (e : E.functor.obj V ≅ W)

/-- Nil and cons squares give a complete algebra isomorphism. No
equation for a fold or for a recursively defined operation is an input. -/
def mappedListConstructorsIso (A : ListAlgebra V) (B : ListAlgebra W)
    (i : E.functor.obj A.carrier ≅ B.carrier)
    (hn : E.functor.map A.nil ≫ i.hom = terminalComparison E.functor ≫ B.nil)
    (hc : E.functor.map A.cons ≫ i.hom =
      prodComparison E.functor V A.carrier ≫ prod.map e.hom i.hom ≫ B.cons) :
    (mappedListAlgebra E V W e A).asAlgebra ≅ B.asAlgebra := by
  refine constructorsIso (mappedListAlgebra E V W e A) B i ?_ ?_
  · change (inv (terminalComparison E.functor) ≫ E.functor.map A.nil) ≫ i.hom = B.nil
    rw [Category.assoc,hn,← Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  · change (prod.map e.inv (𝟙 _) ≫ inv (prodComparison E.functor V A.carrier) ≫
      E.functor.map A.cons) ≫ i.hom = prod.map (𝟙 W) i.hom ≫ B.cons
    simp only [Category.assoc]
    rw [hc]
    simp only [IsIso.inv_hom_id_assoc,prod.map_map_assoc,e.inv_hom_id,
      Category.id_comp]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
