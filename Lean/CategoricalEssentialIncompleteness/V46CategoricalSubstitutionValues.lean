/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionConstructors
public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibility
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsent

/-! # Substitution constructor equations on generalized inputs -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

theorem term_fold_original_value {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.1) :
    prod.lift p a ≫ S.substitutionFold.1.left ≫ prod.snd ≫ prod.fst = a := by
  have hb : prod.lift a p ≫ (prod.braiding S.algebra.a.1 S.substitutionParameters).hom =
      prod.lift p a := by
    apply prod.hom_ext <;> simp [prod.braiding_hom]
  have h := congrArg (fun k => prod.lift a p ≫ k) S.termSubstitution_original
  simp only [← Category.assoc] at h
  rw [hb] at h
  simpa only [Category.assoc, prod.lift_fst] using h

theorem formula_fold_original_value {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.2) :
    prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd ≫ prod.fst = a := by
  have hb : prod.lift a p ≫ (prod.braiding S.algebra.a.2 S.substitutionParameters).hom =
      prod.lift p a := by
    apply prod.hom_ext <;> simp [prod.braiding_hom]
  have h := congrArg (fun k => prod.lift a p ≫ k) S.formulaSubstitution_original
  simp only [← Category.assoc] at h
  rw [hb] at h
  simpa only [Category.assoc, prod.lift_fst] using h

theorem negation_fold_value {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.2) :
    prod.lift p (a ≫ S.negationConstructor) ≫ S.substitutionFold.2.left ≫ prod.snd =
      prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd ≫ S.negationSubstitutionPair := by
  have h := congrArg (fun k => prod.lift p a ≫ k.left ≫ prod.snd) S.negation_fold_in_slice
  simpa [constantFamilyFunctor, Over.comp_left, Category.assoc, prod.lift_map_assoc] using h

theorem equality_fold_value {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.1) :
    prod.lift p (prod.lift a b ≫ S.equalityConstructor) ≫
        S.substitutionFold.2.left ≫ prod.snd =
      prod.lift (prod.lift p a ≫ S.substitutionFold.1.left ≫ prod.snd)
        (prod.lift p b ≫ S.substitutionFold.1.left ≫ prod.snd) ≫
          S.equalitySubstitutionPair := by
  let l : Over.mk p ⟶ constantFamily S.substitutionParameters S.algebra.a.1 ⨯
      constantFamily S.substitutionParameters S.algebra.a.1 :=
    prod.lift (Over.homMk (prod.lift p a) (by simp [constantFamily]))
      (Over.homMk (prod.lift p b) (by simp [constantFamily]))
  have h := congrArg (fun k => (l ≫ k).left ≫ prod.snd) S.equality_fold_in_slice
  simpa [l, constantFamilyFunctor, constantProductComparison, Over.comp_left,
    Category.assoc, prod.comp_lift_assoc, prod.lift_snd] using h

theorem implication_fold_value {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift a b ≫ S.implicationConstructor) ≫
        S.substitutionFold.2.left ≫ prod.snd =
      prod.lift (prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd)
        (prod.lift p b ≫ S.substitutionFold.2.left ≫ prod.snd) ≫
          S.implicationSubstitutionPair := by
  let l : Over.mk p ⟶ constantFamily S.substitutionParameters S.algebra.a.2 ⨯
      constantFamily S.substitutionParameters S.algebra.a.2 :=
    prod.lift (Over.homMk (prod.lift p a) (by simp [constantFamily]))
      (Over.homMk (prod.lift p b) (by simp [constantFamily]))
  have h := congrArg (fun k => (l ≫ k).left ≫ prod.snd) S.implication_fold_in_slice
  simpa [l, constantFamilyFunctor, constantProductComparison, Over.comp_left,
    Category.assoc, prod.comp_lift_assoc, prod.lift_snd] using h

theorem quantified_formula_pair_fold :
    prod.map (𝟙 S.substitutionParameters) S.quantifierConstructor ≫
        S.substitutionFold.2.left ≫ prod.snd =
      S.quantifierFoldInput ≫ S.quantifierSubstitutionPair := by
  have hs := S.quantifier_fold_in_slice
  rw [← Category.assoc, ← Category.assoc] at hs
  have h := congrArg (fun k => k.left ≫ prod.snd) hs
  change (prod.map (𝟙 S.substitutionParameters) S.quantifierConstructor ≫
      S.substitutionFold.2.left) ≫ prod.snd =
    (((parameterStep S.substitutionParameters V S.algebra.a.2 ≫
      prod.map (𝟙 (constantFamily S.substitutionParameters V)) S.substitutionFold.2) ≫
        constantProductComparison S.substitutionParameters V S.substitutionCarriers.2).left ≫
          (parameterHom S.quantifierSubstitutionPair).left) ≫ prod.snd at h
  rw [S.quantifier_fold_input_slice] at h
  simpa only [Category.assoc, parameterHom, Over.homMk_left, prod.lift_snd] using h

theorem quantifier_fold_value {W : D} (p : W ⟶ S.substitutionParameters)
    (y : W ⟶ V) (a : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift y a ≫ S.quantifierConstructor) ≫
        S.substitutionFold.2.left ≫ prod.snd =
      prod.lift p (prod.lift y (prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd)) ≫
        S.quantifierSubstitutionPair := by
  have h := congrArg (fun k => prod.lift p (prod.lift y a) ≫ k) S.quantified_formula_pair_fold
  simpa [quantifierFoldInput, Category.assoc, prod.comp_lift_assoc, prod.lift_map_assoc] using h

theorem closed_formula_fold_value {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.2)
    (ha : a ≫ S.formulaOccurrences = terminal.from W ≫ S.lists.algebra.nil) :
    prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd = prod.lift a (a ≫ coprod.inr) := by
  have hm : prod.lift (p ≫ prod.fst) (a ≫ S.formulaOccurrences) ≫
      S.lists.membership S.decidableVariables = Two.constant W false := by
    rw [ha, S.lists.membership_nil_general]
  have hs := S.formula_substitution_absent_names a (p ≫ prod.fst) (p ≫ prod.snd) hm
  have hp : prod.lift (p ≫ prod.fst) (p ≫ prod.snd) = p := by
    apply prod.hom_ext <;> simp
  rw [hp] at hs
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.lift_fst] using S.formula_fold_original_value p a
  · have hb : prod.lift a p ≫ (prod.braiding S.algebra.a.2 S.substitutionParameters).hom =
        prod.lift p a := by
      apply prod.hom_ext <;> simp [prod.braiding_hom]
    simp only [formulaSubstitutionOption, ← Category.assoc] at hs
    erw [hb] at hs
    simpa only [Category.assoc, prod.lift_snd] using hs

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
