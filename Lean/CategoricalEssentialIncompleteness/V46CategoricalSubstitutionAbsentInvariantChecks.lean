/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentInvariant

/-! Exact generic conditional equality and constructed equalizer-algebra signatures. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
section Conditional
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
example {X Y Z : D} (b : X ⟶ Two D) (original result : X ⟶ Y)
    (h : ConditionalInvariant.Holds b original result) (k : Z ⟶ X)
    (hb : k ≫ b = Two.constant Z false) : k ≫ result = k ≫ original :=
  ConditionalInvariant.fixed_of_false h k hb
example {V X : D} (E : DecidableVariables V) (x y : X ⟶ V) :
    prod.lift x y ≫ E.test = prod.lift y x ≫ E.test := E.test_reverse x y
end Conditional
section Algebra
variable {C : Type u} [Category.{v} C] [HasEqualizers C] {F : C ⥤ C}
variable (A B : Endofunctor.Algebra F) (hA : IsInitial A) {Z : C} (f g : B.a ⟶ Z)
variable (closed : ∀ {X : C} (m : X ⟶ B.a), m ≫ f = m ≫ g →
  (F.map m ≫ B.str) ≫ f = (F.map m ≫ B.str) ≫ g)
example : (AlgebraInvariant.equalizerAlgebra B f g closed).a = equalizer f g := rfl
example : (AlgebraInvariant.equalizerInclusion B f g closed).f = equalizer.ι f g := rfl
example : (hA.to B).f ≫ f = (hA.to B).f ≫ g :=
  AlgebraInvariant.fold_equalizes A B hA f g closed
end Algebra
