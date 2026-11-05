import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionModels

/-! The model comparison assumes preservation of sums and pullbacks only. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
  (K : D ⥤ Type) [PreservesLimitsOfShape WalkingCospan K]
  [PreservesColimitsOfShape (Discrete WalkingPair) K] (Q : D) (n : ℕ)
example : IsPullback (K.map (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n))
    (K.map (𝟙 (finitePower Q n))) (K.map (OptionPowers.collect Q n))
    (K.map (coprod.inr : finitePower Q n ⟶ OptionSyntax.obj (finitePower Q n))) :=
  OptionModels.collect_map_isPullback K Q n
