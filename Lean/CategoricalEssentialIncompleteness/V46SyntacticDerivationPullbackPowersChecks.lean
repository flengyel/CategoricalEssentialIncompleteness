import CategoricalEssentialIncompleteness.V46SyntacticDerivationPullbackPowers

/-! The nullary and all ordered finite powers preserve actual pullback squares. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.PullbackPowers
variable {D : Type u} [Category.{v} D] [Regular D] {P X Y Z : D}
  {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (n : ℕ)
example : IsPullback (finitePowerMap a n) (finitePowerMap b n)
    (finitePowerMap f n) (finitePowerMap g n) := power h n
example : IsPullback (finitePowerMap a 0) (finitePowerMap b 0)
    (finitePowerMap f 0) (finitePowerMap g 0) := power h 0
