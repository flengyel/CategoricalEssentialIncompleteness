/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedOptionConstructors

/-! # Independent statements for Option computations with internal parameters -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open ParameterizedOption

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P W U Y Z : D} (f : P ⨯ Y ⟶ Z) (p : W ⟶ P)

example : map f p (OptionSyntax.fail : W ⟶ OptionSyntax.obj Y) = OptionSyntax.fail := map_fail f p
example (y : W ⟶ Y) : map f p (y ≫ coprod.inr) = prod.lift p y ≫ f ≫ coprod.inr :=
  map_ok f p y
example (a : W ⟶ OptionSyntax.obj Y) (k : U ⟶ W) :
    k ≫ map f p a = map f (k ≫ p) (k ≫ a) := map_precomp f p a k
example {A : D} (y : W ⟶ Y) (a : W ⟶ OptionSyntax.obj A) :
    map f p (OptionSyntax.mask y a) = OptionSyntax.mask (prod.lift p y ≫ f) a :=
  map_mask f p y a
example (b : W ⟶ Two D) (a₀ a₁ : W ⟶ OptionSyntax.obj Y) :
    map f p (Two.branch b a₀ a₁) = Two.branch b (map f p a₀) (map f p a₁) :=
  map_branch f p b a₀ a₁
example {Y' Z' : D} (g : P ⨯ Y' ⟶ Z') (h : Y ⟶ Y') (j : Z ⟶ Z')
    (hh : prod.map (𝟙 P) h ≫ g = f ≫ j) (a : W ⟶ OptionSyntax.obj Y) :
    map g p (a ≫ OptionSyntax.map h) = map f p a ≫ OptionSyntax.map j :=
  map_natural f g h j hh p a
example {Y' Z' : D} (g : P ⨯ Y' ⟶ Z') (h : Y ⨯ Y ⟶ Y') (j : Z ⨯ Z ⟶ Z')
    (hw : ∀ {A : D} (p : A ⟶ P) (y z : A ⟶ Y),
      prod.lift p (prod.lift y z ≫ h) ≫ g =
        prod.lift (prod.lift p y ≫ f) (prod.lift p z ≫ f) ≫ j)
    (a b : W ⟶ OptionSyntax.obj Y) :
    map g p (prod.lift a b ≫ OptionSyntax.binary h) =
      prod.lift (map f p a) (map f p b) ≫ OptionSyntax.binary j := map_binary f g h j hw p a b
example {V Y' : D} (g : P ⨯ Y' ⟶ Z) (h : V ⨯ Y ⟶ Y')
    (hw : ∀ {A : D} (p : A ⟶ P) (v : A ⟶ V) (y : A ⟶ Y),
      prod.lift p (prod.lift v y ≫ h) ≫ g = prod.lift p y ≫ f)
    (v : W ⟶ V) (a : W ⟶ OptionSyntax.obj Y) :
    map g p (prod.lift v a ≫ OptionSyntax.coefficient h) = map f p a :=
  map_ignore_coefficient f g h hw p v a
example {V A B C : D} (h : V ⨯ A ⟶ B) (v : W ⟶ V)
    (a : W ⟶ OptionSyntax.obj A) (w : W ⟶ C) :
    OptionSyntax.mask w (prod.lift v a ≫ OptionSyntax.coefficient h) = OptionSyntax.mask w a :=
  mask_coefficient h v a w

#print axioms ParameterizedOption.map
#print axioms ParameterizedOption.comp_map_fail
#print axioms ParameterizedOption.comp_map_ok
#print axioms ParameterizedOption.map_fail
#print axioms ParameterizedOption.map_ok
#print axioms ParameterizedOption.map_precomp
#print axioms ParameterizedOption.map_mask
#print axioms ParameterizedOption.map_branch
#print axioms ParameterizedOption.map_natural
#print axioms ParameterizedOption.map_natural_value
#print axioms ParameterizedOption.map_binary_ok
#print axioms ParameterizedOption.map_binary
#print axioms ParameterizedOption.map_ignore_coefficient
#print axioms ParameterizedOption.mask_coefficient
