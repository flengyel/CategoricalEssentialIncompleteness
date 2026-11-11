/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryInterpretedSubstitutionHom

/-! # Formula substitution under the interpretation of nullary predicates

Initiality in the substitution-parameter slice identifies the two algebra
morphisms. The induced morphism on admissible substitutions is then a
pullback lift.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

theorem substitution_fold_comparison :
    S.substitutionFold ≫ (substitutionComparisonHom S Q f).f =
      (interpretedSubstitutionHom S Q f).f := by
  have h := (S.stable S.substitutionParameters).hom_ext
    ((S.stable S.substitutionParameters).to S.substitutionAlgebra ≫ substitutionComparisonHom S Q f)
    (interpretedSubstitutionHom S Q f)
  exact congrArg Endofunctor.Algebra.Hom.f h

theorem formula_pair_fold_comparison :
    S.substitutionFold.2.left ≫ prod.snd ≫ (substitutionCarrierMap S Q f).2 =
      interpretedFormulaPair S Q f := by
  have h := congrArg Prod.snd (substitution_fold_comparison S Q f)
  change S.substitutionFold.2 ≫
      (constantFamilyFunctor S.substitutionParameters).map (substitutionCarrierMap S Q f).2 =
    parameterHom (interpretedFormulaPair S Q f) at h
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simpa [constantFamilyFunctor, parameterHom, Over.comp_left, Category.assoc] using hh

theorem formula_substitution_option :
    S.formulaSubstitutionOption ≫ OptionSyntax.map (interpretation S Q f).2 =
      prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) ≫
        Q.formulaSubstitutionOption := by
  have h := congrArg (fun k => k ≫ prod.snd) (formula_pair_fold_comparison S Q f)
  have hs : S.substitutionFold.2.left ≫ prod.snd ≫ prod.snd ≫
      OptionSyntax.map (interpretation S Q f).2 =
      prod.map (substitutionParameterMap S Q f) (interpretation S Q f).2 ≫
        Q.substitutionFold.2.left ≫ prod.snd ≫ prod.snd := by
    simpa [substitutionCarrierMap, interpretedFormulaPair, Category.assoc] using h
  have hb : (prod.braiding S.algebra.a.2 S.substitutionParameters).hom ≫
      prod.map (substitutionParameterMap S Q f) (interpretation S Q f).2 =
      prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) ≫
        (prod.braiding Q.algebra.a.2 Q.substitutionParameters).hom := by
    apply prod.hom_ext <;> simp [prod.braiding_hom]
  calc
    S.formulaSubstitutionOption ≫ OptionSyntax.map (interpretation S Q f).2 =
        (prod.braiding S.algebra.a.2 S.substitutionParameters).hom ≫
          (S.substitutionFold.2.left ≫ prod.snd ≫ prod.snd ≫
            OptionSyntax.map (interpretation S Q f).2) := by
      simp only [CategoricalSyntax.formulaSubstitutionOption, Category.assoc]
    _ = (prod.braiding S.algebra.a.2 S.substitutionParameters).hom ≫
        (prod.map (substitutionParameterMap S Q f) (interpretation S Q f).2 ≫
          Q.substitutionFold.2.left ≫ prod.snd ≫ prod.snd) := congrArg (fun k => _ ≫ k) hs
    _ = ((prod.braiding S.algebra.a.2 S.substitutionParameters).hom ≫
        prod.map (substitutionParameterMap S Q f) (interpretation S Q f).2) ≫
          Q.substitutionFold.2.left ≫ prod.snd ≫ prod.snd := by
      simp only [Category.assoc]
    _ = prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) ≫
        Q.formulaSubstitutionOption := by
      rw [hb]
      simp only [CategoricalSyntax.formulaSubstitutionOption, Category.assoc]

def admissibleInterpretation : S.admissibleSubstitution ⟶ Q.admissibleSubstitution :=
  pullback.lift
    (S.admissibleInclusion ≫
      prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f))
    (S.formulaSubstitution ≫ (interpretation S Q f).2) (by
      rw [Category.assoc, ← formula_substitution_option S Q f,
        ← Category.assoc, S.formulaSubstitution_square, Category.assoc, OptionSyntax.map_ok]
      simp only [Category.assoc])

@[reassoc (attr := simp)] theorem admissibleInterpretation_inclusion :
    admissibleInterpretation S Q f ≫ Q.admissibleInclusion =
      S.admissibleInclusion ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem admissibleInterpretation_result :
    admissibleInterpretation S Q f ≫ Q.formulaSubstitution =
      S.formulaSubstitution ≫ (interpretation S Q f).2 := pullback.lift_snd _ _ _

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
