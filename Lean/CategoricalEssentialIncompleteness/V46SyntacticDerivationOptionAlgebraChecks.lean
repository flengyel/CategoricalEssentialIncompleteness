import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionAlgebra

/-! The total validator algebra uses only rule data and internal premise equality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
  {F : D} {N : ℕ} (R : RulePresentation F N)
  (E : ∀ i : Fin (N + 1), DecidableVariables (finitePower F i.val))
example : Endofunctor.Algebra (PolynomialComparison.ordinary R) := OptionAlgebra.validator R E
example (Q : Over F) (α : R.inference.obj Q ⟶ Q) :
    Endofunctor.Algebra (PolynomialComparison.ordinary R) := OptionAlgebra.algebra R E Q α
