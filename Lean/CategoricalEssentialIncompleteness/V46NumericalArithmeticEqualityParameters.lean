/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticRuleParameters

/-! # The equality scheme retains both independent admissibility pullbacks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.EqualityParameters
open Coordinates SubstitutionParameters SubstitutionDomains RuleParameters NamedArithmeticSignature
local notation "K" => numericalInterpretation
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax

@[reassoc] theorem name_coordinate : equalityBaseIso.hom ≫
    (K).map ((prod.fst (C := PredicateCategory 𝗣𝗔) (X := (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (S₀).algebra.a.2)) (Y := (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.1 (S₀).algebra.a.1))) ≫ prod.fst (C := PredicateCategory 𝗣𝗔)) =
      prod.fst ≫ prod.fst ≫ variableIso.hom := by
  exact pairedIso_fst_fst variableIso formulaIso (pairedIso termIso termIso)

@[reassoc] theorem formula_coordinate : equalityBaseIso.hom ≫
    (K).map ((prod.fst (C := PredicateCategory 𝗣𝗔) (X := (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (S₀).algebra.a.2)) (Y := (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.1 (S₀).algebra.a.1))) ≫ prod.snd (C := PredicateCategory 𝗣𝗔)) =
      prod.fst ≫ prod.snd ≫ formulaIso.hom := by
  exact pairedIso_fst_snd variableIso formulaIso (pairedIso termIso termIso)

@[reassoc] theorem left_coordinate : equalityBaseIso.hom ≫
    (K).map ((prod.snd (C := PredicateCategory 𝗣𝗔) (X := (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (S₀).algebra.a.2)) (Y := (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.1 (S₀).algebra.a.1))) ≫ prod.fst (C := PredicateCategory 𝗣𝗔)) =
      prod.snd ≫ prod.fst ≫ termIso.hom := by
  exact pairedIso_snd_fst (pairedIso variableIso formulaIso) termIso termIso

@[reassoc] theorem right_coordinate : equalityBaseIso.hom ≫
    (K).map ((prod.snd (C := PredicateCategory 𝗣𝗔) (X := (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (S₀).algebra.a.2)) (Y := (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.1 (S₀).algebra.a.1))) ≫ prod.snd (C := PredicateCategory 𝗣𝗔)) =
      prod.snd ≫ prod.snd ≫ termIso.hom := by
  exact pairedIso_snd_snd (pairedIso variableIso formulaIso) termIso termIso

theorem first_input : (S).equalityFirstInput ≫ formulaInputIso.hom =
    equalityBaseIso.hom ≫ (K).map (S₀).equalityFirstInput := by
  simp only [CategoricalSyntax.equalityFirstInput,formulaInputIso,pairedIso_lift,
    post_mapped_lift,formula_coordinate,name_coordinate,left_coordinate,
    parameterIso,pairedIso_lift,Category.assoc]

theorem second_input : (S).equalitySecondInput ≫ formulaInputIso.hom =
    equalityBaseIso.hom ≫ (K).map (S₀).equalitySecondInput := by
  simp only [CategoricalSyntax.equalitySecondInput,formulaInputIso,pairedIso_lift,
    post_mapped_lift,formula_coordinate,name_coordinate,right_coordinate,
    parameterIso,pairedIso_lift,Category.assoc]

def firstIso : pullback (S).equalityFirstInput (S).admissibleInclusion ≅
    (K).obj (pullback (S₀).equalityFirstInput (S₀).admissibleInclusion) :=
  pullbackComparison (S₀).equalityFirstInput (S₀).admissibleInclusion
    (S).equalityFirstInput (S).admissibleInclusion equalityBaseIso admissibleIso formulaInputIso
    first_input forward_inclusion.symm

def secondIso : pullback (S).equalitySecondInput (S).admissibleInclusion ≅
    (K).obj (pullback (S₀).equalitySecondInput (S₀).admissibleInclusion) :=
  pullbackComparison (S₀).equalitySecondInput (S₀).admissibleInclusion
    (S).equalitySecondInput (S).admissibleInclusion equalityBaseIso admissibleIso formulaInputIso
    second_input forward_inclusion.symm

@[reassoc] theorem first_inclusion : firstIso.hom ≫
    (K).map (pullback.fst (S₀).equalityFirstInput (S₀).admissibleInclusion) =
      pullback.fst (S).equalityFirstInput (S).admissibleInclusion ≫ equalityBaseIso.hom :=
  pullbackComparison_fst _ _ _ _ _ _ _ _ _

@[reassoc] theorem second_inclusion : secondIso.hom ≫
    (K).map (pullback.fst (S₀).equalitySecondInput (S₀).admissibleInclusion) =
      pullback.fst (S).equalitySecondInput (S).admissibleInclusion ≫ equalityBaseIso.hom :=
  pullbackComparison_fst _ _ _ _ _ _ _ _ _

@[reassoc] theorem first_admissible : firstIso.hom ≫
    (K).map (pullback.snd (S₀).equalityFirstInput (S₀).admissibleInclusion) =
      pullback.snd (S).equalityFirstInput (S).admissibleInclusion ≫ admissibleIso.hom :=
  pullbackComparison_snd _ _ _ _ _ _ _ _ _

@[reassoc] theorem second_admissible : secondIso.hom ≫
    (K).map (pullback.snd (S₀).equalitySecondInput (S₀).admissibleInclusion) =
      pullback.snd (S).equalitySecondInput (S).admissibleInclusion ≫ admissibleIso.hom :=
  pullbackComparison_snd _ _ _ _ _ _ _ _ _

/-- The two substitutions share only their `(x,φ,u,t)` base coordinates;
each keeps its own success point. -/
def equalityIso : (S).equalitySchemeParameters ≅ (K).obj (S₀).equalitySchemeParameters :=
  pullbackComparison
    (pullback.fst (S₀).equalityFirstInput (S₀).admissibleInclusion)
    (pullback.fst (S₀).equalitySecondInput (S₀).admissibleInclusion)
    (pullback.fst (S).equalityFirstInput (S).admissibleInclusion)
    (pullback.fst (S).equalitySecondInput (S).admissibleInclusion)
    firstIso secondIso equalityBaseIso first_inclusion.symm second_inclusion.symm

private theorem mapped_chain
    {A B C : PredicateCategory 𝗣𝗔} {X Y Z : NumericalTuples.Object}
    {h : X ⟶ (K).obj A} {p : X ⟶ Y} {j : Y ⟶ (K).obj B}
    {q : Y ⟶ Z} {k : Z ⟶ (K).obj C} {f : A ⟶ B} {g : B ⟶ C}
    (hf : h ≫ (K).map f = p ≫ j) (hg : j ≫ (K).map g = q ≫ k) :
    h ≫ (K).map (f ≫ g) = (p ≫ q) ≫ k := by
  rw [(K).map_comp,← Category.assoc,hf,Category.assoc,hg,← Category.assoc]

private abbrev equality_fst :=
  pullbackComparison_fst
    (pullback.fst (S₀).equalityFirstInput (S₀).admissibleInclusion)
    (pullback.fst (S₀).equalitySecondInput (S₀).admissibleInclusion)
    (pullback.fst (S).equalityFirstInput (S).admissibleInclusion)
    (pullback.fst (S).equalitySecondInput (S).admissibleInclusion)
    firstIso secondIso equalityBaseIso first_inclusion.symm second_inclusion.symm

private abbrev equality_snd :=
  pullbackComparison_snd
    (pullback.fst (S₀).equalityFirstInput (S₀).admissibleInclusion)
    (pullback.fst (S₀).equalitySecondInput (S₀).admissibleInclusion)
    (pullback.fst (S).equalityFirstInput (S).admissibleInclusion)
    (pullback.fst (S).equalitySecondInput (S).admissibleInclusion)
    firstIso secondIso equalityBaseIso first_inclusion.symm second_inclusion.symm

@[reassoc] theorem equality_inclusion : equalityIso.hom ≫ (K).map (S₀).equalitySchemeInclusion =
    (S).equalitySchemeInclusion ≫ equalityBaseIso.hom := by
  exact mapped_chain equality_fst first_inclusion

@[reassoc] theorem equality_first_admissible : equalityIso.hom ≫ (K).map (S₀).equalityFirstAdmissible =
    (S).equalityFirstAdmissible ≫ admissibleIso.hom := by
  exact mapped_chain equality_fst first_admissible

@[reassoc] theorem equality_second_admissible : equalityIso.hom ≫ (K).map (S₀).equalitySecondAdmissible =
    (S).equalitySecondAdmissible ≫ admissibleIso.hom := by
  exact mapped_chain equality_snd second_admissible

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.EqualityParameters
