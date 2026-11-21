/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportAlgebras


/-! # Constructor comparisons for transported list algebras -/

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
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable [HasFiniteProducts D] [HasFiniteCoproducts D]

example (E : C ≌ D) (V : C) (W : D) (e : E.functor.obj V ≅ W)
    (A : ListAlgebra V) (B : ListAlgebra W) (i : E.functor.obj A.carrier ≅ B.carrier)
    (hn : E.functor.map A.nil ≫ i.hom = terminalComparison E.functor ≫ B.nil)
    (hc : E.functor.map A.cons ≫ i.hom =
      prodComparison E.functor V A.carrier ≫ prod.map e.hom i.hom ≫ B.cons) :
    (mappedListAlgebra E V W e A).asAlgebra ≅ B.asAlgebra :=
  mappedListConstructorsIso E V W e A B i hn hc
