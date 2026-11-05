import CategoricalEssentialIncompleteness.V46SyntacticDerivationSliceInitial

/-! Initiality in the validator slice is derived from ordinary initiality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SliceInitial
variable {D : Type u} [Category.{v} D] (S : D ⥤ D) (V A : Endofunctor.Algebra S)
  (hA : IsInitial A)
example : IsInitial (algebra S V A hA) := initial S V A hA
example (B : Endofunctor.Algebra (functor S V)) : algebra S V A hA ⟶ B := fold S V A hA B
