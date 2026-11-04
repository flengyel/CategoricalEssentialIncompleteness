import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityOptions

/-! The actual lifted constructors return the expected successful result. -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

example {X V Y Z : D} (h : V ⨯ Y ⟶ Z) (v : X ⟶ V) (y : X ⟶ Y) :
    prod.lift v (y ≫ coprod.inr) ≫ OptionSyntax.coefficient h =
      prod.lift v y ≫ h ≫ coprod.inr := OptionSyntax.coefficient_ok h v y

example {X Y Z : D} (h : Y ⨯ Y ⟶ Z) (y z : X ⟶ Y) :
    prod.lift (y ≫ coprod.inr) (z ≫ coprod.inr) ≫ OptionSyntax.binary h =
      prod.lift y z ≫ h ≫ coprod.inr := OptionSyntax.binary_ok h y z

example {Y Z : D} (h : Y ⨯ Y ⟶ Z) :
    prod.map (coprod.inr : Y ⟶ OptionSyntax.obj Y) coprod.inr ≫ OptionSyntax.binary h =
      h ≫ coprod.inr := OptionSyntax.binary_ok_map h
