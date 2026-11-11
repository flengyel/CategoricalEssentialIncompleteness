/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AlgebraTransport

/-! # Algebra transport with independent universes and arbitrary endofunctors -/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.AlgebraTransport

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (E : C ≌ D) (F : C ⥤ C) (G : D ⥤ D)
variable (α : F ⋙ E.functor ≅ E.functor ⋙ G)

example : Endofunctor.Algebra F ≌ Endofunctor.Algebra G := equivalence E α

example (A : Endofunctor.Algebra F) (hA : IsInitial A) :
    IsInitial (mappedAlgebra E α A) := initial E α A hA

example (A : Endofunctor.Algebra F) :
    IsInitial A ≃ IsInitial (mappedAlgebra E α A) := initialIff E α A

example (A B : Endofunctor.Algebra F) (f : A.a ⟶ B.a) :
    G.map (E.functor.map f) ≫ (mappedAlgebra E α B).str =
        (mappedAlgebra E α A).str ≫ E.functor.map f ↔
      F.map f ≫ B.str = A.str ≫ f := hom_condition_iff E α A B f
