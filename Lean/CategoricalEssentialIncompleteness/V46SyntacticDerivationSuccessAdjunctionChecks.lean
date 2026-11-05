import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessAdjunction

/-! The actual success-pullback functor has the explicitly constructed option extension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessAdjunction
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D] (F : D)
example : Over.pullback (some F) ⊣ extend F := adjunction F
example (X : Over (OptionSyntax.obj F)) (Q : Over F) :
    ((Over.pullback (some F)).obj X ⟶ Q) ≃ (X ⟶ (extend F).obj Q) := homEquiv F X Q
