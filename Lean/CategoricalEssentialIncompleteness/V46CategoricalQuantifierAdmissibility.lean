/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibilityOptions
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentity

/-! The exact quantified admissibility decomposition for the named-variable fold. -/

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

/-- The option-success decomposition of the quantifier algebra step. -/
theorem quantifier_result_success :
    OptionSyntax.success S.quantifierSubstitutionResult =
      Two.fiberSubobject S.quantifierEquality true ⊔
        (Two.fiberSubobject S.quantifierEquality false ⊓
          Two.fiberSubobject S.captureAllowed true ⊓
            OptionSyntax.success (prod.snd ≫ prod.snd ≫ prod.snd)) := by
  unfold quantifierSubstitutionResult
  rw [OptionSyntax.success_branch, OptionSyntax.success_branch,
    OptionSyntax.success_fail, OptionSyntax.success_ok]
  simp only [inf_bot_eq, bot_sup_eq, inf_top_eq]
  rw [OptionSyntax.success_coefficient_comp, prod.lift_snd]
  rw [sup_comm, inf_assoc]

/-- Original and computed body data fed into the quantified fold step. -/
def quantifierFoldInput : S.substitutionParameters ⨯ (V ⨯ S.algebra.a.2) ⟶
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) :=
  prod.lift prod.fst (prod.lift (prod.snd ≫ prod.fst)
    (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ S.substitutionFold.2.left ≫ prod.snd))

theorem quantifier_fold_input_slice :
    ((parameterStep S.substitutionParameters V S.algebra.a.2 ≫
      prod.map (𝟙 (constantFamily S.substitutionParameters V)) S.substitutionFold.2) ≫
        constantProductComparison S.substitutionParameters V S.substitutionCarriers.2).left =
      S.quantifierFoldInput := by
  let k := parameterStep S.substitutionParameters V S.algebra.a.2 ≫
    prod.map (𝟙 (constantFamily S.substitutionParameters V)) S.substitutionFold.2
  apply prod.hom_ext
  · have h := Over.w (k ≫
      constantProductComparison S.substitutionParameters V S.substitutionCarriers.2)
    change (k ≫ constantProductComparison S.substitutionParameters V
      S.substitutionCarriers.2).left ≫ prod.fst = prod.fst at h
    simpa only [quantifierFoldInput, prod.lift_fst] using h
  · have hc : (constantProductComparison S.substitutionParameters V
          S.substitutionCarriers.2).left ≫ prod.snd =
        prod.lift (listStepHead S.substitutionParameters V S.substitutionCarriers.2)
          (listStepValue S.substitutionParameters V S.substitutionCarriers.2) :=
      prod.lift_snd _ _
    change (k.left ≫ (constantProductComparison S.substitutionParameters V
      S.substitutionCarriers.2).left) ≫ prod.snd = S.quantifierFoldInput ≫ prod.snd
    rw [Category.assoc, hc, quantifierFoldInput, prod.lift_snd]
    rw [prod.comp_lift]
    exact congrArg₂ prod.lift (parameterStep_map_head S.substitutionFold.2)
      (parameterStep_map_value S.substitutionFold.2)

/-- The quantifier constructor equation of the substitution fold, retaining its parameter
in the slice. -/
theorem quantifier_fold_in_slice :
    (constantFamilyFunctor S.substitutionParameters).map S.quantifierConstructor ≫
        S.substitutionFold.2 =
      parameterStep S.substitutionParameters V S.algebra.a.2 ≫
        prod.map (𝟙 (constantFamily S.substitutionParameters V)) S.substitutionFold.2 ≫
          constantProductComparison S.substitutionParameters V S.substitutionCarriers.2 ≫
            parameterHom S.quantifierSubstitutionPair := by
  have h := congrArg Prod.snd S.substitutionFold_commutes
  change (((SyntaxPolynomial.formulaExpression V π d).withParameters
      S.substitutionParameters).eval.map S.substitutionFold) ≫ S.substitutionAlgebra.str.2 =
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters).str.2 ≫
        S.substitutionFold.2 at h
  rw [S.formula_parameter_structure S.substitutionParameters] at h
  let j : constantFamily S.substitutionParameters (V ⨯ S.algebra.a.2) ⟶
      (((SyntaxPolynomial.formulaExpression V π d).withParameters
        S.substitutionParameters).eval.obj
          (constantFamily S.substitutionParameters S.algebra.a.1,
            constantFamily S.substitutionParameters S.algebra.a.2)) :=
    parameterStep S.substitutionParameters V S.algebra.a.2 ≫ coprod.inr
  have hh := congrArg (fun k => j ≫ k) h
  simpa only [j, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, CategoryTheory.Functor.const, CategoryTheory.Prod.snd,
    substitutionAlgebra, coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, SyntaxPolynomial.parameterComparison, prod.map_id_id,
    Category.id_comp, Category.assoc, parameterStep_comparison_assoc] using hh.symm

theorem quantified_formula_fold :
    prod.map (𝟙 S.substitutionParameters) S.quantifierConstructor ≫
        S.substitutionFold.2.left ≫ prod.snd ≫ prod.snd =
      S.quantifierFoldInput ≫ S.quantifierSubstitutionResult := by
  have hs := S.quantifier_fold_in_slice
  rw [← Category.assoc, ← Category.assoc] at hs
  have h := congrArg (fun k => k.left ≫ prod.snd ≫ prod.snd) hs
  change (prod.map (𝟙 S.substitutionParameters) S.quantifierConstructor ≫
      S.substitutionFold.2.left) ≫ prod.snd ≫ prod.snd =
    (((parameterStep S.substitutionParameters V S.algebra.a.2 ≫
      prod.map (𝟙 (constantFamily S.substitutionParameters V)) S.substitutionFold.2) ≫
        constantProductComparison S.substitutionParameters V S.substitutionCarriers.2).left ≫
          (parameterHom S.quantifierSubstitutionPair).left) ≫ prod.snd ≫ prod.snd at h
  rw [S.quantifier_fold_input_slice] at h
  simpa only [Category.assoc, parameterHom, Over.homMk_left,
    prod.lift_snd_assoc, quantifierSubstitutionPair, prod.lift_snd] using h

/-- The manuscript's `B = (V × Fm) × E`. -/
def quantifierAdmissibilityParameters : D := (V ⨯ S.algebra.a.2) ⨯ S.substitutionParameters

/-- The displayed map `q` forms the quantified original formula. -/
def quantifiedInput : S.quantifierAdmissibilityParameters ⟶
    S.algebra.a.2 ⨯ S.substitutionParameters := prod.map S.quantifierConstructor (𝟙 _)

/-- The displayed map `p` forgets the bound variable and retains the body. -/
def quantifiedBody : S.quantifierAdmissibilityParameters ⟶
    S.algebra.a.2 ⨯ S.substitutionParameters :=
  prod.lift (prod.fst ≫ prod.snd) prod.snd

def quantifiedFoldInput : S.quantifierAdmissibilityParameters ⟶
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) :=
  prod.lift prod.snd (prod.lift (prod.fst ≫ prod.fst)
    (S.quantifiedBody ≫ (prod.braiding _ _).hom ≫ S.substitutionFold.2.left ≫ prod.snd))

def quantifiedEquality : S.quantifierAdmissibilityParameters ⟶ Two D :=
  prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.fst) ≫ S.decidableVariables.test

def quantifiedCapture : S.quantifierAdmissibilityParameters ⟶ Two D :=
  Two.binary Bool.or
    (Two.unary Bool.not
      (prod.lift (prod.snd ≫ prod.fst)
        (prod.fst ≫ prod.snd ≫ S.formulaOccurrences) ≫
          S.lists.membership S.decidableVariables))
    (Two.unary Bool.not
      (prod.lift (prod.fst ≫ prod.fst)
        (prod.snd ≫ prod.snd ≫ S.termOccurrences) ≫
          S.lists.membership S.decidableVariables))

@[simp, reassoc] theorem quantified_fold_equality :
    S.quantifiedFoldInput ≫ S.quantifierEquality = S.quantifiedEquality := by
  simp [quantifiedFoldInput, quantifierEquality, quantifiedEquality]

@[simp, reassoc] theorem quantified_fold_option :
    S.quantifiedFoldInput ≫ (prod.snd ≫ prod.snd ≫ prod.snd) =
      S.quantifiedBody ≫ S.formulaSubstitutionOption := by
  simp only [quantifiedFoldInput, Category.assoc, prod.lift_snd_assoc,
    formulaSubstitutionOption]

@[simp, reassoc] theorem quantified_body_original :
    S.quantifiedBody ≫ (prod.braiding _ _).hom ≫ S.substitutionFold.2.left ≫
        prod.snd ≫ prod.fst = prod.fst ≫ prod.snd := by
  rw [S.formulaSubstitution_original]
  simp [quantifiedBody]

@[simp, reassoc] theorem quantified_fold_capture :
    S.quantifiedFoldInput ≫ S.captureAllowed = S.quantifiedCapture := by
  simp [quantifiedFoldInput, captureAllowed, quantifiedCapture, Category.assoc,
    -prod.braiding_hom]
  rw [S.quantified_body_original_assoc]

@[reassoc] theorem quantified_fold_input_reassociate :
    (prod.braiding (V ⨯ S.algebra.a.2) S.substitutionParameters).hom ≫
        S.quantifierFoldInput = S.quantifiedFoldInput := by
  apply prod.hom_ext
  · simp [quantifierFoldInput, quantifiedFoldInput, prod.braiding_hom]
  · apply prod.hom_ext
    · simp [quantifierFoldInput, quantifiedFoldInput, prod.braiding_hom]
    · have h : (prod.braiding (V ⨯ S.algebra.a.2) S.substitutionParameters).hom ≫
          prod.lift prod.fst (prod.snd ≫ prod.snd) =
        S.quantifiedBody ≫ (prod.braiding S.algebra.a.2 S.substitutionParameters).hom := by
        apply prod.hom_ext <;> simp [quantifiedBody, prod.braiding_hom]
      simpa only [quantifierFoldInput, quantifiedFoldInput, prod.comp_lift_assoc,
        prod.lift_snd, prod.lift_snd_assoc, Category.assoc] using
          congrArg (fun k => k ≫ S.substitutionFold.2.left ≫ prod.snd) h

/-- The formula fold has the displayed quantified branch equation on the manuscript's
parameter object `B`. -/
theorem quantified_substitution_equation :
    S.quantifiedInput ≫ S.formulaSubstitutionOption =
      S.quantifiedFoldInput ≫ S.quantifierSubstitutionResult := by
  unfold quantifiedInput formulaSubstitutionOption
  rw [← Category.assoc, braid_natural]
  simp only [Category.assoc, S.quantified_formula_fold,
    S.quantified_fold_input_reassociate_assoc]

/-- The manuscript's admissibility-subobject identity, with pullback intersection and join
in the subobject lattice of `B`. -/
theorem quantified_admissibility_subobjects :
    (Subobject.pullback S.quantifiedInput).obj (Subobject.mk S.admissibleInclusion) =
      Two.fiberSubobject S.quantifiedEquality true ⊔
        (Two.fiberSubobject S.quantifiedEquality false ⊓
          Two.fiberSubobject S.quantifiedCapture true ⊓
            (Subobject.pullback S.quantifiedBody).obj (Subobject.mk S.admissibleInclusion)) := by
  have ha : Subobject.mk S.admissibleInclusion =
      OptionSyntax.success S.formulaSubstitutionOption :=
    (OptionSyntax.success_eq_mk _).symm
  rw [ha, ← OptionSyntax.success_comp, S.quantified_substitution_equation,
    OptionSyntax.success_comp, S.quantifier_result_success]
  rw [SubobjectPredicates.pullback_sup, Subobject.inf_pullback, Subobject.inf_pullback]
  rw [← Two.fiberSubobject_comp, ← Two.fiberSubobject_comp, ← Two.fiberSubobject_comp,
    ← OptionSyntax.success_comp, S.quantified_fold_equality, S.quantified_fold_capture,
    S.quantified_fold_option, OptionSyntax.success_comp]

/-- The second summand in the displayed disjoint admissibility join. -/
def quantifiedDistinctAdmissibility : Subobject S.quantifierAdmissibilityParameters :=
  Two.fiberSubobject S.quantifiedEquality false ⊓
    Two.fiberSubobject S.quantifiedCapture true ⊓
      (Subobject.pullback S.quantifiedBody).obj (Subobject.mk S.admissibleInclusion)

theorem quantified_admissibility_disjoint :
    Two.fiberSubobject S.quantifiedEquality true ⊓ S.quantifiedDistinctAdmissibility = ⊥ := by
  apply bot_unique
  calc
    _ ≤ Two.fiberSubobject S.quantifiedEquality true ⊓
        Two.fiberSubobject S.quantifiedEquality false :=
      inf_le_inf_left _ (inf_le_left.trans inf_le_left)
    _ = ⊥ := (Two.boundFibers_isCompl S.quantifiedEquality).symm.inf_eq_bot

/-- The displayed join is represented by a coproduct inclusion into `B`. -/
def quantifiedAdmissibilityCoproduct :
    (Two.fiberSubobject S.quantifiedEquality true : D) ⨿
        (S.quantifiedDistinctAdmissibility : D) ⟶ S.quantifierAdmissibilityParameters :=
  coprod.desc (Two.fiberSubobject S.quantifiedEquality true).arrow
    S.quantifiedDistinctAdmissibility.arrow

instance quantifiedAdmissibilityCoproduct_mono : Mono S.quantifiedAdmissibilityCoproduct :=
  (PresentationLemmas.mono_copair_iff _ _).mpr (by
    simpa only [Subobject.mk_arrow] using S.quantified_admissibility_disjoint)

theorem quantified_admissibility_coproduct :
    Subobject.mk S.quantifiedAdmissibilityCoproduct =
      (Subobject.pullback S.quantifiedInput).obj (Subobject.mk S.admissibleInclusion) := by
  rw [← imageSubobject_mono S.quantifiedAdmissibilityCoproduct]
  change imageSubobject (coprod.desc (Two.fiberSubobject S.quantifiedEquality true).arrow
      S.quantifiedDistinctAdmissibility.arrow) = _
  rw [PresentationLemmas.image_copair, imageSubobject_mono, imageSubobject_mono,
    Subobject.mk_arrow, Subobject.mk_arrow]
  exact S.quantified_admissibility_subobjects.symm

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
