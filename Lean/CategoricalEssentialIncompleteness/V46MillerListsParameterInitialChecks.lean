/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsParameterInitial


/-! # Direct list initiality in every uniform parameter slice -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (R : Total.TotalCategory P) (V : Total.Carrier P)
example : IsInitial (Lists.parameterAlgebra R V).asAlgebra := Lists.parameterInitial R V
example (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    (Lists.parameterFold R V B).left ≫ B.a.hom=(Lists.family R V).hom := Over.w _
example (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    (Lists.parameterAlgebra R V).asAlgebra.str ≫ (Lists.parameterFoldHom R V B).f=
      (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P))).map (Lists.parameterFoldHom R V B).f ≫ B.str :=
  (Lists.parameterFoldHom R V B).h.symm
example (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P))))
    (f : (Lists.parameterAlgebra R V).asAlgebra ⟶ B) :
    f=Lists.parameterFoldHom R V B := Lists.parameterFoldHom_unique R V B f
