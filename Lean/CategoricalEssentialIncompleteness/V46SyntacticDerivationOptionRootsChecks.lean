import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionRoots

/-! Failure extension preserves the exact successful root-input pullback. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {A Q Z W : PredicateCategory T}
  (g : A ⨯ Q ⟶ OptionSyntax.obj Z) (m : W ⟶ A ⨯ Q) (h : W ⟶ Z)
  (hp : IsPullback m h g (coprod.inr : Z ⟶ OptionSyntax.obj Z))
example : IsPullback (m ≫ prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q)) h
    (OptionPowers.liftRoot g) (coprod.inr : Z ⟶ OptionSyntax.obj Z) :=
  OptionRoots.predicate T g m h hp
