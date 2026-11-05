import CategoricalEssentialIncompleteness.V46SyntacticDerivationAlgebraAdjunction

/-! Initial-algebra transfer, with the adjunction and comparison explicitly typed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.AlgebraAdjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {F : C ⥤ C} {G : D ⥤ D} (θ : F ⋙ L ≅ L ⋙ G)
  (A : Endofunctor.Algebra F) (hA : IsInitial A)
example : IsInitial (leftAlgebra θ A) := initial adj θ A hA
example (B : Endofunctor.Algebra G) :
    (leftAlgebra θ A ⟶ B) ≃ (A ⟶ rightAlgebra adj θ B) := homEquiv adj θ A B
