/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxAlgebra

/-! # Checks for the free-syntax interpretation prerequisites -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]
variable {V : D}


open NullarySyntaxAlgebra
variable {X : D} (A B : Algebra V X) (m : A.a ⟶ B.a)
variable (hv : variableConstructor A ≫ m.1 = variableConstructor B)
variable (he : equalityConstructor A ≫ m.2 = prod.map m.1 m.1 ≫ equalityConstructor B)
variable (ha : atomConstructor A ≫ m.2 = atomConstructor B)
variable (hn : negationConstructor A ≫ m.2 = m.2 ≫ negationConstructor B)
variable (hi : implicationConstructor A ≫ m.2 = prod.map m.2 m.2 ≫ implicationConstructor B)
variable (hq : quantifierConstructor A ≫ m.2 = prod.map (𝟙 V) m.2 ≫ quantifierConstructor B)

example : A ⟶ B := homOfConstructors m hv he ha hn hi hq
example : (homOfConstructors m hv he ha hn hi hq).f = m := rfl

#print axioms CategoricalEssentialIncompleteness.V46.NullarySyntaxAlgebra.homOfConstructors

example [HasStrictInitialObjects D] (P : D) : IsInitial (constantFamily P (⊥_ D)) :=
  constantInitial P

#print axioms CategoricalEssentialIncompleteness.V46.NullarySyntaxAlgebra.constantInitial
#print axioms CategoricalEssentialIncompleteness.V46.NullarySyntaxAlgebra.homOfConstructorsOfInitial
