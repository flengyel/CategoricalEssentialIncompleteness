import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionPowers

/-! The nullary tuple and every ordered finite option power are included. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionPowers
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D] (Q : D) (n : ℕ)
example : finitePower (OptionSyntax.obj Q) n ⟶ OptionSyntax.obj (finitePower Q n) := collect Q n
example : finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n ≫ collect Q n = coprod.inr :=
  collect_some Q n
example : collect Q 0 = (coprod.inr : ⊤_ D ⟶ OptionSyntax.obj (⊤_ D)) := rfl
