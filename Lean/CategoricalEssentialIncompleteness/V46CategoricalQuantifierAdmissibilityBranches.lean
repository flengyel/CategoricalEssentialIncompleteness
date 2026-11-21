/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibility

/-! The substitution results on the two quantified domain summands. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

@[reassoc] theorem quantified_fold_original :
    S.quantifiedFoldInput ≫ S.quantifierOriginal = prod.fst ≫ S.quantifierConstructor := by
  simp [quantifiedFoldInput, quantifierOriginal, Category.assoc, -prod.braiding_hom]

theorem quantified_equal_name {X : D} (k : X ⟶ S.quantifierAdmissibilityParameters)
    (he : k ≫ S.quantifiedEquality = Two.constant X true) :
    k ≫ S.quantifiedInput ≫ S.formulaSubstitutionOption =
      k ≫ prod.fst ≫ S.quantifierConstructor ≫ coprod.inr := by
  have he' : (k ≫ S.quantifiedFoldInput) ≫ S.quantifierEquality =
      Two.constant X true := by
    simpa only [Category.assoc, S.quantified_fold_equality] using he
  have hb : (k ≫ S.quantifiedFoldInput) ≫ S.quantifierSubstitutionResult =
      (k ≫ S.quantifiedFoldInput) ≫ S.quantifierOriginal ≫ coprod.inr := by
    unfold quantifierSubstitutionResult
    exact Two.comp_branch _ _ _ _ true he'
  calc
    _ = k ≫ S.quantifiedFoldInput ≫ S.quantifierSubstitutionResult := by
      rw [S.quantified_substitution_equation]
    _ = k ≫ S.quantifiedFoldInput ≫ S.quantifierOriginal ≫ coprod.inr := by
      simpa only [Category.assoc] using hb
    _ = _ := by rw [S.quantified_fold_original_assoc]

/-- The second domain summand carries the induced map to the body's admissibility
pullback. -/
def quantifiedDistinctBody : (S.quantifiedDistinctAdmissibility : D) ⟶
    S.admissibleSubstitution := by
  have h : S.quantifiedDistinctAdmissibility ≤
      Subobject.mk (pullback.fst S.quantifiedBody S.admissibleInclusion) := by
    rw [← Subobject.pullback_obj_mk
      (IsPullback.of_hasPullback S.quantifiedBody S.admissibleInclusion).flip]
    exact inf_le_right
  exact Subobject.ofLEMk _ (pullback.fst S.quantifiedBody S.admissibleInclusion) h ≫
    pullback.snd S.quantifiedBody S.admissibleInclusion

@[reassoc] theorem quantifiedDistinctBody_square :
    S.quantifiedDistinctBody ≫ S.admissibleInclusion =
      S.quantifiedDistinctAdmissibility.arrow ≫ S.quantifiedBody := by
  unfold quantifiedDistinctBody
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, Subobject.ofLEMk_comp]

theorem quantified_distinct_success {X : D} (k : X ⟶ S.quantifierAdmissibilityParameters)
    (he : k ≫ S.quantifiedEquality = Two.constant X false)
    (hc : k ≫ S.quantifiedCapture = Two.constant X true)
    (a : X ⟶ S.admissibleSubstitution)
    (ha : k ≫ S.quantifiedBody = a ≫ S.admissibleInclusion) :
    k ≫ S.quantifiedInput ≫ S.formulaSubstitutionOption =
      prod.lift (k ≫ prod.fst ≫ prod.fst) (a ≫ S.formulaSubstitution) ≫
        S.quantifierConstructor ≫ coprod.inr := by
  have he' : (k ≫ S.quantifiedFoldInput) ≫ S.quantifierEquality =
      Two.constant X false := by
    simpa only [Category.assoc, S.quantified_fold_equality] using he
  have hc' : (k ≫ S.quantifiedFoldInput) ≫ S.captureAllowed =
      Two.constant X true := by
    simpa only [Category.assoc, S.quantified_fold_capture] using hc
  have hr := S.quantifierSubstitution_distinct_allowed (k ≫ S.quantifiedFoldInput) he' hc'
  have hr' : k ≫ S.quantifiedFoldInput ≫ S.quantifierSubstitutionResult =
      prod.lift (k ≫ prod.fst ≫ prod.fst)
        (k ≫ S.quantifiedBody ≫ S.formulaSubstitutionOption) ≫
          OptionSyntax.coefficient S.quantifierConstructor := by
    simpa [quantifiedFoldInput, formulaSubstitutionOption, Category.assoc] using hr
  have hs : k ≫ S.quantifiedBody ≫ S.formulaSubstitutionOption =
      (a ≫ S.formulaSubstitution) ≫ coprod.inr := by
    rw [← Category.assoc, ha, Category.assoc, S.formulaSubstitution_square,
      ← Category.assoc]
  calc
    _ = k ≫ S.quantifiedFoldInput ≫ S.quantifierSubstitutionResult := by
      rw [S.quantified_substitution_equation]
    _ = _ := hr'.trans (by
      rw [hs]
      simpa only [Category.assoc] using OptionSyntax.coefficient_ok S.quantifierConstructor
        (k ≫ prod.fst ≫ prod.fst) (a ≫ S.formulaSubstitution))
/-- The inclusion of a truth-value subobject satisfies its defining equation. -/
theorem fiber_subobject_value {X : D} (b : X ⟶ Two D) (c : Bool) (A : Subobject X)
    (h : A ≤ Two.fiberSubobject b c) : A.arrow ≫ b = Two.constant (A : D) c := by
  let l := Subobject.ofLEMk A (Two.fiberι b c) h
  have hl : l ≫ Two.fiberι b c = A.arrow := Subobject.ofLEMk_comp h
  rw [← hl, Category.assoc, Two.fiberι_comp, Two.comp_constant]

theorem quantified_equal_result :
    (Two.fiberSubobject S.quantifiedEquality true).arrow ≫
        S.quantifiedInput ≫ S.formulaSubstitutionOption =
      (Two.fiberSubobject S.quantifiedEquality true).arrow ≫
        prod.fst ≫ S.quantifierConstructor ≫ coprod.inr :=
  S.quantified_equal_name _ (fiber_subobject_value S.quantifiedEquality true _ le_rfl)

theorem quantified_distinct_result :
    S.quantifiedDistinctAdmissibility.arrow ≫ S.quantifiedInput ≫
        S.formulaSubstitutionOption =
      prod.lift (S.quantifiedDistinctAdmissibility.arrow ≫ prod.fst ≫ prod.fst)
        (S.quantifiedDistinctBody ≫ S.formulaSubstitution) ≫
          S.quantifierConstructor ≫ coprod.inr := by
  have he := fiber_subobject_value S.quantifiedEquality false
    S.quantifiedDistinctAdmissibility (inf_le_left.trans inf_le_left)
  have hc := fiber_subobject_value S.quantifiedCapture true
    S.quantifiedDistinctAdmissibility (inf_le_left.trans inf_le_right)
  exact S.quantified_distinct_success S.quantifiedDistinctAdmissibility.arrow he hc
    S.quantifiedDistinctBody S.quantifiedDistinctBody_square.symm

/-- Admissible input on the equal-name summand, returning the original quantified formula
independently of recursive success. -/
def quantifiedEqualAdmissible : (Two.fiberSubobject S.quantifiedEquality true : D) ⟶
    S.admissibleSubstitution :=
  pullback.lift ((Two.fiberSubobject S.quantifiedEquality true).arrow ≫ S.quantifiedInput)
    ((Two.fiberSubobject S.quantifiedEquality true).arrow ≫ prod.fst ≫ S.quantifierConstructor)
    (by simpa only [Category.assoc] using S.quantified_equal_result)

/-- Admissible input on the distinct-name, capture-allowed, admissible-body summand, with
the recursively substituted body. -/
def quantifiedDistinctAdmissible : (S.quantifiedDistinctAdmissibility : D) ⟶
    S.admissibleSubstitution :=
  pullback.lift (S.quantifiedDistinctAdmissibility.arrow ≫ S.quantifiedInput)
    (prod.lift (S.quantifiedDistinctAdmissibility.arrow ≫ prod.fst ≫ prod.fst)
      (S.quantifiedDistinctBody ≫ S.formulaSubstitution) ≫ S.quantifierConstructor)
    (by simpa only [Category.assoc] using S.quantified_distinct_result)

@[simp, reassoc] theorem quantifiedEqualAdmissible_inclusion :
    S.quantifiedEqualAdmissible ≫ S.admissibleInclusion =
      (Two.fiberSubobject S.quantifiedEquality true).arrow ≫ S.quantifiedInput :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem quantifiedEqualAdmissible_result :
    S.quantifiedEqualAdmissible ≫ S.formulaSubstitution =
      (Two.fiberSubobject S.quantifiedEquality true).arrow ≫
        prod.fst ≫ S.quantifierConstructor := pullback.lift_snd _ _ _

@[simp, reassoc] theorem quantifiedDistinctAdmissible_inclusion :
    S.quantifiedDistinctAdmissible ≫ S.admissibleInclusion =
      S.quantifiedDistinctAdmissibility.arrow ≫ S.quantifiedInput := pullback.lift_fst _ _ _

@[simp, reassoc] theorem quantifiedDistinctAdmissible_result :
    S.quantifiedDistinctAdmissible ≫ S.formulaSubstitution =
      prod.lift (S.quantifiedDistinctAdmissibility.arrow ≫ prod.fst ≫ prod.fst)
        (S.quantifiedDistinctBody ≫ S.formulaSubstitution) ≫ S.quantifierConstructor :=
  pullback.lift_snd _ _ _

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
