import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentSteps

/-! Actual named-variable constructor calculations under the induction invariant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example {X : D} (p : X ⟶ S.substitutionParameters) (y : X ⟶ V)
    (ha : S.termAbsenceTest p (y ≫ S.variableConstructor) = Two.constant X false) :
    prod.lift p y ≫ S.variableSubstitutionPair ≫ prod.snd = y ≫ S.variableConstructor :=
  S.variable_absent_value p y ha

example {X : D} (p : X ⟶ S.substitutionParameters) (y : X ⟶ V)
    (a : X ⟶ S.substitutionCarriers.2) (good : S.formulaPairGood p a)
    (ha : S.formulaAbsenceTest p
      (prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor) = Two.constant X false) :
    prod.lift p (prod.lift y a) ≫ S.quantifierSubstitutionResult =
      prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor ≫ coprod.inr :=
  S.quantifier_absent_value p y a good ha
