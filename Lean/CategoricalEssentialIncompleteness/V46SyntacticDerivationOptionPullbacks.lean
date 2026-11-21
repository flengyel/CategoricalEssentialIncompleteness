/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionModels
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular

/-! Success-domain pullbacks in the predicate category and every parameter slice. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionPullbacks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

theorem predicate_of_models {P X Y Z : PredicateCategory T}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hw : a ≫ f = b ≫ g)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      IsPullback ((PredicateInterpretation.functor T M).map a)
        ((PredicateInterpretation.functor T M).map b)
        ((PredicateInterpretation.functor T M).map f)
        ((PredicateInterpretation.functor T M).map g)) : IsPullback a b f g := by
  let : ReflectsLimitsOfShape WalkingCospan (PredicateInterpretation.allModels T) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply IsPullback.of_map (PredicateInterpretation.allModels T) hw
  apply IsPullback.of_forall_isPullback_app
  intro m
  exact h m.as.carrier

theorem slice_of_models {P : PredicateCategory T} {W X Y Z : Over P}
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hw : a ≫ f = b ≫ g)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      IsPullback ((PredicateInterpretation.functor T M).map a.left)
        ((PredicateInterpretation.functor T M).map b.left)
        ((PredicateInterpretation.functor T M).map f.left)
        ((PredicateInterpretation.functor T M).map g.left)) : IsPullback a b f g := by
  let U := Over.forget P ⋙ PredicateInterpretation.allModels T
  let : ReflectsLimitsOfShape WalkingCospan U :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply IsPullback.of_map U hw
  apply IsPullback.of_forall_isPullback_app
  intro m
  exact h m.as.carrier

theorem collect (Q : PredicateCategory T) (n : ℕ) :
    IsPullback (finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n)
      (𝟙 (finitePower Q n)) (OptionPowers.collect Q n)
      (coprod.inr : finitePower Q n ⟶ OptionSyntax.obj (finitePower Q n)) := by
  apply predicate_of_models T (by simpa only [Category.id_comp] using OptionPowers.collect_some Q n)
  intro M _ _
  exact OptionModels.collect_map_isPullback (PredicateInterpretation.functor T M) Q n


end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionPullbacks
