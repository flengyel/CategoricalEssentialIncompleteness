/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionModels
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionPullbacks

/-! Exact success domains after adjoining the child-failure branch. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionRoots
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

def chart (A Q : D) : A ⨯ Q ≅
    pullback (prod.snd : A ⨯ OptionSyntax.obj Q ⟶ OptionSyntax.obj Q) coprod.inr where
  hom := pullback.lift (prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q)) prod.snd (by simp)
  inv := prod.lift (pullback.fst _ coprod.inr ≫ prod.fst) (pullback.snd _ coprod.inr)
  hom_inv_id := by
    apply prod.hom_ext <;> simp
  inv_hom_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext
      · simp
      · simp only [Category.assoc, pullback.lift_fst, prod.map_snd, prod.lift_snd_assoc]
        simpa only [Category.id_comp] using (pullback.condition
          (f := (prod.snd : A ⨯ OptionSyntax.obj Q ⟶ OptionSyntax.obj Q))
          (g := (coprod.inr : Q ⟶ OptionSyntax.obj Q))).symm
    · simp

@[simp, reassoc] theorem chart_fst (A Q : D) :
    (chart A Q).hom ≫ pullback.fst _ coprod.inr =
      prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q) := pullback.lift_fst _ _ _

theorem map_isPullback (K : D ⥤ Type) [PreservesLimitsOfShape WalkingCospan K]
    [PreservesColimitsOfShape (Discrete WalkingPair) K]
    {A Q Z W : D} (g : A ⨯ Q ⟶ OptionSyntax.obj Z)
    (m : W ⟶ A ⨯ Q) (h : W ⟶ Z)
    (hp : IsPullback m h g (coprod.inr : Z ⟶ OptionSyntax.obj Z)) :
    IsPullback (K.map (m ≫ prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q)))
      (K.map h) (K.map (OptionPowers.liftRoot g))
      (K.map (coprod.inr : Z ⟶ OptionSyntax.obj Z)) := by
  have hc : IsPullback (m ≫ (chart A Q).hom) h ((chart A Q).inv ≫ g)
      (coprod.inr : Z ⟶ OptionSyntax.obj Z) := by
    apply hp.of_iso (Iso.refl _) (chart A Q) (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp
    · simp
  have hr := OptionModels.caseOf_map_isPullback K
    (prod.snd : A ⨯ OptionSyntax.obj Q ⟶ OptionSyntax.obj Q)
    ((chart A Q).inv ≫ g) (m ≫ (chart A Q).hom) h hc
  change IsPullback (K.map (m ≫ prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q)))
    (K.map h) (K.map (SumFibers.caseOf
      (prod.snd : A ⨯ OptionSyntax.obj Q ⟶ OptionSyntax.obj Q) OptionSyntax.fail
      ((chart A Q).inv ≫ g))) (K.map (coprod.inr : Z ⟶ OptionSyntax.obj Z))
  simpa only [Category.assoc, chart_fst] using hr

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionRoots

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionRoots
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

theorem predicate {A Q Z W : PredicateCategory T} (g : A ⨯ Q ⟶ OptionSyntax.obj Z)
    (m : W ⟶ A ⨯ Q) (h : W ⟶ Z)
    (hp : IsPullback m h g (coprod.inr : Z ⟶ OptionSyntax.obj Z)) :
    IsPullback (m ≫ prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q)) h
      (OptionPowers.liftRoot g) (coprod.inr : Z ⟶ OptionSyntax.obj Z) := by
  apply OptionPullbacks.predicate_of_models T (by
    rw [Category.assoc, OptionPowers.liftRoot_some, hp.w])
  intro M _ _
  exact map_isPullback (PredicateInterpretation.functor T M) g m h hp

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionRoots
