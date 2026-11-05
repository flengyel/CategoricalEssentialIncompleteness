import CategoricalEssentialIncompleteness.V46SyntacticDerivationModelPullbacks

/-! A concrete conservative family supplies the success pullbacks, without an evaluator field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
  {J : Type w} (K : D ⥤ (Discrete J ⥤ Type)) [K.ReflectsIsomorphisms]
  [PreservesLimitsOfShape WalkingCospan K]
  [PreservesColimitsOfShape (Discrete WalkingPair) K] (Q : D) (n : ℕ)
example : IsPullback (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n)
    (𝟙 (finitePower Q n)) (OptionPowers.collect Q n)
    (coprod.inr : finitePower Q n ⟶ OptionSyntax.obj (finitePower Q n)) :=
  ModelPullbacks.collect K Q n
