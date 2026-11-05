import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionRoots

/-! Success geometry from a concrete conservative family of interpretations.
This is instantiated by all arithmetic models for predicates, and by the
actual inverse equivalence followed by those models for total split maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.ModelPullbacks
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
  {J : Type w} (K : D ⥤ (Discrete J ⥤ Type)) [K.ReflectsIsomorphisms]
  [PreservesLimitsOfShape WalkingCospan K]
  [PreservesColimitsOfShape (Discrete WalkingPair) K]

abbrev evaluationFunctor (j : J) : D ⥤ Type := K ⋙ (evaluation (Discrete J) Type).obj ⟨j⟩

omit [FinitaryExtensive D] [PreservesColimitsOfShape (Discrete WalkingPair) K] in
theorem reflect {P X Y Z : D} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hw : a ≫ f = b ≫ g)
    (h : ∀ j : J, IsPullback ((evaluationFunctor K j).map a) ((evaluationFunctor K j).map b)
      ((evaluationFunctor K j).map f) ((evaluationFunctor K j).map g)) : IsPullback a b f g := by
  let : ReflectsLimitsOfShape WalkingCospan K := reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply IsPullback.of_map K hw
  apply IsPullback.of_forall_isPullback_app
  intro j
  exact h j.as

include K in
theorem collect (Q : D) (n : ℕ) :
    IsPullback (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n)
      (𝟙 (finitePower Q n)) (OptionPowers.collect Q n)
      (coprod.inr : finitePower Q n ⟶ OptionSyntax.obj (finitePower Q n)) := by
  apply reflect K (by simpa only [Category.id_comp] using OptionPowers.collect_some Q n)
  intro j
  exact OptionModels.collect_map_isPullback (evaluationFunctor K j) Q n

include K in
theorem liftRoot {A Q Z W : D} (g : A ⨯ Q ⟶ OptionSyntax.obj Z)
    (m : W ⟶ A ⨯ Q) (h : W ⟶ Z)
    (hp : IsPullback m h g (coprod.inr : Z ⟶ OptionSyntax.obj Z)) :
    IsPullback (m ≫ prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q)) h
      (OptionPowers.liftRoot g) (coprod.inr : Z ⟶ OptionSyntax.obj Z) := by
  apply reflect K (by rw [Category.assoc, OptionPowers.liftRoot_some, hp.w])
  intro j
  exact OptionRoots.map_isPullback (evaluationFunctor K j) g m h hp

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.ModelPullbacks
